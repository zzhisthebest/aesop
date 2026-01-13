/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Codetic.Script.Main
public import Codetic.Search.ExpandSafePrefix
public import Codetic.Tree.Check
public import Codetic.Tree.ExtractProof
public import Codetic.Tree.ExtractScript
public import Codetic.Tree.Tracing
import Codetic.Frontend.Extension
import Codetic.Search.Queue
import Codetic.Tree.Free
import Codetic.Tracing

public section

open Lean
open Lean.Elab.Tactic (liftMetaTacticAux TacticM)
open Lean.Parser.Tactic (tacticSeq)
open Lean.Meta

namespace Codetic

variable [Codetic.Queue Q]
--己。
partial def nextActiveGoal : SearchM Q GoalRef := do
  let some gref ← popGoal?
    | throwError "codetic/expandNextGoal: internal error: no active goals left"
  if ! (← (← gref.get).isActive) then
    nextActiveGoal
  else
    return gref

def expandNextGoal : SearchM Q Unit := do
  let gref ← nextActiveGoal
  let g ← gref.get
  let (initialGoal, initialMetaState) ←
    g.currentGoalAndMetaState (← getRootMetaState)
  let result ← withCodeticTraceNode .steps
    (fmt g.id g.priority initialGoal initialMetaState) do
    initialMetaState.runMetaM' do
      codetic_trace[steps] "Initial goal:{indentD initialGoal}"
    let maxRappDepth := (← read).options.maxRuleApplicationDepth
    if maxRappDepth != 0 && (← gref.get).depth >= maxRappDepth then
      codetic_trace[steps] "Treating the goal as unprovable since it is beyond the maximum rule application depth ({maxRappDepth})."
      gref.markForcedUnprovable
      setMaxRuleApplicationDepthReached
      return .failed
    let result ← expandGoal gref--核心代码
    let currentIteration ← getIteration
    gref.modify λ g => g.setLastExpandedInIteration currentIteration
    if ← (← gref.get).isActive then
      enqueueGoals #[gref]
    return result
  match result with
  | .proved newRapps | .succeeded newRapps => traceNewRapps newRapps--多分支合并语法
  | .failed => return
  where
    --这个函数仅仅是记录日志
    fmt (id : GoalId) (priority : Percent) (initialGoal : MVarId)
        (initialMetaState : Meta.SavedState)
        (result : Except Exception RuleResult) : SearchM Q MessageData := do
      let tgt ← initialMetaState.runMetaM' do
        initialGoal.withContext do
          addMessageContext $ toMessageData (← initialGoal.getType)
      return m!"{exceptRuleResultToEmoji (·.toEmoji) result} (G{id}) [{priority.toHumanString}] ⋯ ⊢ {tgt}"
    --这个函数仅仅是记录日志
    traceNewRapps (newRapps : Array RappRef) : SearchM Q Unit := do
      codetic_trace[steps] do
        for rref in newRapps do
          let r ← rref.get
          r.withHeadlineTraceNode .steps
            (transform := λ msg => return m!"{newNodeEmoji} " ++ msg) do
            withCodeticTraceNode .steps (λ _ => return "Metadata") do
              r.traceMetadata .steps
          r.metaState.runMetaM' do
            r.forSubgoalsM λ gref => do
              let g ← gref.get
              g.withHeadlineTraceNode .steps
                (transform := λ msg => return m!"{newNodeEmoji} " ++ msg) do
                codetic_trace![steps] g.preNormGoal
                withCodeticTraceNode .steps (λ _ => return "Metadata") do
                  g.traceMetadata .steps

def checkGoalLimit : SearchM Q (Option MessageData) := do
  let maxGoals := (← read).options.maxGoals
  let currentGoals := (← getTree).numGoals
  if maxGoals != 0 && currentGoals >= maxGoals then
    return m!"maximum number of goals ({maxGoals}) reached. Set the 'maxGoals' option to increase the limit."
  return none

def checkRappLimit : SearchM Q (Option MessageData) := do
  let maxRapps := (← read).options.maxRuleApplications
  let currentRapps := (← getTree).numRapps
  if maxRapps != 0 && currentRapps >= maxRapps then
    return m!"maximum number of rule applications ({maxRapps}) reached. Set the 'maxRuleApplications' option to increase the limit."
  return none

--己。
def checkRootUnprovable : SearchM Q (Option MessageData) := do
  let root := (← getTree).root
  if (← root.get).state.isUnprovable then
    let msg ←
      if ← wasMaxRuleApplicationDepthReached then
        pure m!"failed to prove the goal. Some goals were not explored because the maximum rule application depth ({(← read).options.maxRuleApplicationDepth}) was reached. Set option 'maxRuleApplicationDepth' to increase the limit."
      else
        pure m!"failed to prove the goal after exhaustive search."
    return msg
  return none

def getProof? : SearchM Q (Option Expr) := do
  getExprMVarAssignment? (← getRootMVarId)

def finalizeProof : SearchM Q Unit := do
  (← getRootMVarId).withContext do
    extractProof
    let (some proof) ← getProof? | throwError
      "codetic: internal error: root goal is proven but its metavariable is not assigned"
    if (← instantiateMVars proof).hasExprMVar then
      let inner :=
        m!"Proof: {proof}\nUnassigned metavariables: {(← getMVarsNoDelayed proof).map (·.name)}"
      throwError "codetic: internal error: extracted proof has metavariables.{indentD inner}"
    withPPAnalyze do
      codetic_trace[proof] "Final proof:{indentExpr proof}"

def traceScript (completeProof : Bool) : SearchM Q Unit :=
  profiling (λ stats _ elapsed => { stats with script := elapsed }) do
  let options := (← read).options
  if ! options.generateScript then
    return
  let (uscript, proofHasMVars) ←
    if completeProof then extractScript else extractSafePrefixScript
  uscript.checkIfEnabled
  let rootGoal ← getRootMVarId
  let rootState ← getRootMetaState
  codetic_trace[script] "Unstructured script:{indentD $ toMessageData $ ← uscript.renderTacticSeq rootState rootGoal}"
  let sscript? ← uscript.optimize proofHasMVars rootState rootGoal
  checkAndTraceScript uscript sscript? rootState rootGoal options
    (expectCompleteProof := completeProof) "codetic"

def traceTree : SearchM Q Unit := do
  (← (← getRootGoal).get).traceTree .tree

def finishIfProven : SearchM Q Bool := do
  unless (← (← getRootMVarCluster).get).state.isProven do
    return false
  finalizeProof
  traceScript (completeProof := true)
  traceTree
  return true

-- TODO move to Tree directory
/--
This function detects whether the search has made progress, meaning that the
remaining goals after safe prefix expansion are different from the initial goal.
We approximate this by checking whether, after safe prefix expansion, either
of the following statements is true.

- There is a safe rapp.
- A subgoal of the preprocessing rule has been modified during normalisation.

This is an approximation because a safe rule could, in principle, leave the
initial goal unchanged.
-/
def treeHasProgress : TreeM Bool := do
  let resultRef ← IO.mkRef false
  preTraverseDown
    (λ gref => do
      let g ← gref.get
      if let some postGoal := g.normalizationState.normalizedGoal? then
        if postGoal != g.preNormGoal then
          resultRef.set true
          return false
      return true)
    (λ rref => do
      let rule := (← rref.get).appliedRule
      if rule.name == preprocessRule.name then
        return true
      else if rule.isUnsafe then
        return false
      else
        resultRef.set true
        return false)
    (λ _ => return true)
    (.mvarCluster (← getThe Tree).root)
  resultRef.get

def throwCodeticEx (mvarId : MVarId) (remainingSafeGoals : Array MVarId)
    (safePrefixExpansionSuccess : Bool) (msg? : Option MessageData) :
    SearchM Q α := do
  if codetic.smallErrorMessages.get (← getOptions) then
    match msg? with
    | none => throwError "tactic 'codetic' failed"
    | some msg => throwError "tactic 'codetic' failed, {msg}"
  else
    let maxRapps := (← read).options.maxSafePrefixRuleApplications
    let suffix :=
      if remainingSafeGoals.isEmpty then
        m!""
      else
        let gs := .joinSep (remainingSafeGoals.toList.map toMessageData) "\n\n"
        let suffix' :=
          if safePrefixExpansionSuccess then
            m!""
          else
            m!"\nThe safe prefix was not fully expanded because the maximum number of rule applications ({maxRapps}) was reached."
        m!"\nRemaining goals after safe rules:{indentD gs}{suffix'}"
    -- Copy-pasta from `Lean.Meta.throwTacticEx`
    match msg? with
    | none => throwError "tactic 'codetic' failed\nInitial goal:{indentD mvarId}{suffix}"
    | some msg => throwError "tactic 'codetic' failed, {msg}\nInitial goal:{indentD mvarId}{suffix}"


-- When we hit a non-fatal error (i.e. the search terminates without a proof
-- because the root goal is unprovable or because we hit a search limit), we
-- usually:
--
-- - Expand all safe rules as much as possible, starting from the root node,
--   until we hit an unsafe rule. We call this the safe prefix.
-- - Extract the proof term for the safe prefix and report the remaining goals.
--
-- The first step is necessary because a goal can become unprovable due to a
-- sibling being unprovable, without the goal ever being expanded. So if we did
-- not expand the safe rules after the fact, the tactic's output would be
-- sensitive to minor changes in, e.g., rule priority.
def handleNonfatalError (err : MessageData) : SearchM Q (Array MVarId) := do
  let safeExpansionSuccess ← expandSafePrefix
  let safeGoals ← extractSafePrefix
  codetic_trace[proof] do
    match ← getProof? with
    | some proof =>
      (← getRootMVarId).withContext do
        codetic_trace![proof] "{proof}"
    | none => codetic_trace![proof] "<no proof>"
  traceTree
  traceScript (completeProof := false)
  let opts := (← read).options
  if opts.terminal then
    throwCodeticEx (← getRootMVarId) safeGoals safeExpansionSuccess err
  if ! (← treeHasProgress) then
    throwCodeticEx (← getRootMVarId) #[] safeExpansionSuccess "made no progress"
  if opts.warnOnNonterminal && codetic.warn.nonterminal.get (← getOptions) then
    logWarning m!"codetic: {err}"
  if ! safeExpansionSuccess then
    logWarning m!"codetic: safe prefix was not fully expanded because the maximum number of rule applications ({(← read).options.maxSafePrefixRuleApplications}) was reached."
  safeGoals.mapM (clearForwardImplDetailHyps ·)


--己。
partial def searchLoop : SearchM Q (Array MVarId) :=
  withIncRecDepth do
    checkSystem "codetic"
    if let (some err) ← checkRootUnprovable then
      handleNonfatalError err
    else if ← finishIfProven then
      return #[]
    else if let (some err) ← checkGoalLimit then
      handleNonfatalError err
    else if let (some err) ← checkRappLimit then
      handleNonfatalError err
    else
      expandNextGoal
      checkInvariantsIfEnabled
      incrementIteration
      searchLoop

def search (goal : MVarId) (ruleSet? : Option LocalRuleSet := none)
     (options : Codetic.Options := {}) (simpConfig : Simp.Config := {})
     (simpConfigSyntax? : Option Term := none) (stats : Stats := {}) :
     MetaM (Array MVarId × Stats) := do
  goal.checkNotAssigned `codetic
  let options ← options.toOptions'
  let ruleSet ←
    match ruleSet? with
    | none =>
        let rss ← Frontend.getDefaultGlobalRuleSets
        mkLocalRuleSet rss options
    | some ruleSet => pure ruleSet
  let ⟨Q, _⟩ := options.queue
  let go : SearchM _ _ := do
    show SearchM Q _ from
    try searchLoop--核心代码
    finally freeTree
  let ((goals, _, _), stats) ←
    go.run ruleSet options simpConfig simpConfigSyntax? goal |>.run stats
  return (goals, stats)

end Codetic
