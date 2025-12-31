/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Tree.State
public import Aesop.Search.SearchM
public import Aesop.Tree.RunMetaM
public import Batteries.Lean.Meta.SavedState
import Aesop.RuleTac
import Aesop.RuleTac.ElabRuleTerm
import Aesop.Script.SpecificTactics
import Aesop.Search.RuleSelection
import Batteries.Lean.HashSet
import Aesop.Forward.State.ApplyGoalDiff
import Aesop.Search.Expansion.Basic
import Aesop.Search.Expansion.Simp
import Aesop.Tracing

public section

open Lean Lean.Meta Aesop.Script

namespace Aesop

namespace NormM

structure Context where
  options : Options'
  ruleSet : LocalRuleSet
  normSimpContext : NormSimpContext

structure State where
  forwardState : ForwardState
  forwardRuleMatches : ForwardRuleMatches
  deriving Inhabited

end NormM

abbrev NormM := ReaderT NormM.Context $ StateRefT NormM.State BaseM

def getForwardState : NormM ForwardState :=
  return (← getThe NormM.State).forwardState

def getResetForwardState : NormM ForwardState := do
  modifyGetThe NormM.State λ s => (s.forwardState, { s with forwardState := ∅ })

def updateForwardState (fs : ForwardState) (newMatches : Array ForwardRuleMatch)
    (erasedHyps : Std.HashSet FVarId) : NormM Unit :=
  modifyThe NormM.State λ s => { s with
    forwardState := fs
    forwardRuleMatches :=
      s.forwardRuleMatches.update newMatches erasedHyps
        (consumedForwardRuleMatches := #[]) -- We erase the consumed matches separately.
  }

def eraseForwardRuleMatch (m : ForwardRuleMatch) : NormM Unit := do
  modifyThe NormM.State λ s => { s with forwardRuleMatches := s.forwardRuleMatches.erase m }

def applyDiffToForwardState (diff : GoalDiff) : NormM Unit := do
  let fs ← getResetForwardState
  let (fs, ms) ← fs.applyGoalDiff (← read).ruleSet diff
  updateForwardState fs ms diff.removedFVars

inductive NormRuleResult
  | succeeded (goal : MVarId) (steps? : Option (Array Script.LazyStep))
  | proved (steps? : Option (Array Script.LazyStep))

namespace NormRuleResult

def newGoal? : NormRuleResult → Option MVarId
  | succeeded goal .. => goal
  | proved .. => none

def steps? : NormRuleResult → Option (Array Script.LazyStep)
  | .succeeded (steps? := steps?) .. | .proved (steps? := steps?) .. => steps?

end NormRuleResult

def optNormRuleResultEmoji : Option NormRuleResult → String
  | some (.succeeded ..) => ruleSuccessEmoji
  | some (.proved ..) => ruleProvedEmoji
  | none => ruleFailureEmoji

@[inline, always_inline]
def withNormTraceNode (ruleName : DisplayRuleName)
    (k : NormM (Option NormRuleResult)) : NormM (Option NormRuleResult) :=
  withAesopTraceNode .steps fmt do
    let result? ← k
    if let some newGoal := result?.bind (·.newGoal?) then
      aesop_trace[steps] newGoal
    return result?
  where
    fmt (r : Except Exception (Option NormRuleResult)) : NormM MessageData := do
      let emoji := exceptRuleResultToEmoji (optNormRuleResultEmoji ·) r
      return m!"{emoji} {ruleName}"

/-- On success, returns the rule tactic's result, the new forward state and the
new forward rule matches. If `rule` corresponds to some forward rule matches,
returns the matches as well. -/
def runNormRuleTac (rule : NormRule) (input : RuleTacInput) (fs : ForwardState)
    (rs : LocalRuleSet) :
    NormM $
      Option (NormRuleResult × ForwardState × Array ForwardRuleMatch × Std.HashSet FVarId) ×
      Array ForwardRuleMatch := do
  let preMetaState ← show MetaM _ from saveState
  let result? ← runRuleTac rule.tac.run rule.name preMetaState input
  let forwardRuleMatches := rule.tac.forwardRuleMatches? |>.getD #[]
  match result? with
  | .error e =>
    aesop_trace[steps] e.toMessageData
    return (none, forwardRuleMatches)
  | .ok result =>
    let #[rapp] := result.applications
      | err m!"rule did not produce exactly one rule application."
    show MetaM _ from restoreState rapp.postState
    if rapp.goals.isEmpty then
      return (some (.proved rapp.scriptSteps?, fs, #[], ∅), forwardRuleMatches)
    let (#[{ diff, .. }]) := rapp.goals
      | err m!"rule produced more than one subgoal."
    let (fs, ms) ← fs.applyGoalDiff rs diff
    let g := diff.newGoal
    if ← Check.rules.isEnabled then
      let mvars := .ofArray input.mvars.toArray
      let actualMVars ← rapp.postState.runMetaM' g.getMVarDependencies
      if ! actualMVars == mvars then
         err "the goal produced by the rule depends on different metavariables than the original goal."
    let result := .succeeded g rapp.scriptSteps?
    return (some (result, fs, ms, diff.removedFVars), forwardRuleMatches)
  where
    err {α} (msg : MessageData) : MetaM α := throwError
      "aesop: error while running norm rule {rule.name}: {msg}\nThe rule was run on this goal:{indentD $ MessageData.ofGoal input.goal}"

def runNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (rule : IndexMatchResult NormRule) : NormM (Option NormRuleResult) := do
  profilingRule (.ruleName rule.rule.name) (λ result => result.isSome) do
    let ruleInput := {
      indexMatchLocations := rule.locations
      patternSubsts? := rule.patternSubsts?
      options := (← read).options
      hypTypes := (← get).forwardState.hypTypes
      goal, mvars
    }
    withNormTraceNode (.ruleName rule.rule.name) do
      let fs ← getForwardState
      let (result?, consumedForwardRuleMatches) ←
        runNormRuleTac rule.rule ruleInput fs (← read).ruleSet
      for m in consumedForwardRuleMatches do
        eraseForwardRuleMatch m
      let (some (result, fs, ms, removedFVars)) := result?
        | return none
      updateForwardState fs ms removedFVars
      return result

def runFirstNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (rules : Array (IndexMatchResult NormRule)) :
    NormM (Option (DisplayRuleName × NormRuleResult)) := do
  for rule in rules do
    let result? ← runNormRule goal mvars rule
    if let some result := result? then
      return some (rule.rule.name, result)
  return none

def mkNormSimpScriptStep
    (preGoal : MVarId) (postGoal? : Option MVarId)
    (preState postState : Meta.SavedState) (usedTheorems : Simp.UsedSimps)
    (actuallyUsedSimpAll : Bool := false) :
    NormM Script.LazyStep := do
  let ctx := (← read).normSimpContext
  -- 使用实际执行成功的方法，而不是配置的方法
  let simpBuilder :=
    TacticBuilder.simpAllOrSimpAtStar (simpAll := actuallyUsedSimpAll) preGoal
      ctx.configStx? usedTheorems
  let simpOnlyBuilder :=
    TacticBuilder.simpAllOrSimpAtStarOnly (simpAll := actuallyUsedSimpAll) preGoal
      ctx.configStx? usedTheorems
  let tacticBuilders :=
    if (← read).options.useDefaultSimpSet then
      #[simpOnlyBuilder, simpBuilder]
    else
      #[simpOnlyBuilder]
  return {
    postGoals := postGoal?.toArray
    tacticBuilders
    tacticBuilders_ne := by simp only [tacticBuilders]; split <;> simp
    preGoal, preState, postState
  }

/-- 检查名称是否是内部生成的函数（如 match_1 等） -/
private def isInternalGenerated (n : Name) : Bool :=
  let rec checkComponents (name : Name) : Bool :=
    match name with
    | .str parent str =>
      (str.startsWith "match_" ||
       str.startsWith "_") || checkComponents parent
    | .num parent _ => checkComponents parent
    | _ => false
  checkComponents n

/-- 检查定义是否是递归的：如果有 unfoldEqn 就视为递归 -/
private def isRecursiveDef (decl : Name) : MetaM Bool := do
  return (← getUnfoldEqnFor? decl).isSome

/-- 检查常量是否在当前文件中定义（通过命名空间匹配） -/
private def isCurrentFileConstant (decl : Name) : MetaM Bool := do
  -- 排除内部生成的函数
  if isInternalGenerated decl then
    return false
  let env ← getEnv
  if ! env.contains decl then
    return false
  -- 检查是否是定义（def）
  match env.find? decl with
  | some (.defnInfo _) =>
    -- 获取当前命名空间
    let currNamespace ← getCurrNamespace
    -- 如果当前命名空间不是匿名的，检查名称是否在当前命名空间下
    if currNamespace != Name.anonymous then
      if currNamespace.isPrefixOf decl then
        -- 有 unfoldEqn 的视为递归，跳过
        if ← isRecursiveDef decl then
          -- aesop_trace![zzh_custom] " recursive def from simp: {decl}"
          return false
        return true
    return false
  | _ => return false

/-- 收集目标中出现的常量，并过滤出当前文件定义的常量 -/
private def collectCurrentFileConstants (goal : MVarId) : MetaM (Array Name) :=
  goal.withContext do
    let tgt ← instantiateMVars $ ← goal.getType
    let mut constants := tgt.foldConsts (init := ({} : Std.HashSet Name)) λ c acc => acc.insert c
    for ldecl in (← getLCtx) do
      if ! ldecl.isImplementationDetail then
        let type ← instantiateMVars ldecl.type
        constants := type.foldConsts (init := constants) λ c acc => acc.insert c
        if let some value := ldecl.value? then
          let value ← instantiateMVars value
          constants := value.foldConsts (init := constants) λ c acc => acc.insert c
    -- 过滤出当前文件定义的常量
    let mut result := #[]
    -- aesop_trace![zzh_custom] "Found {constants.size} constants in goal"
    for const in constants do
      -- aesop_trace![zzh_custom] "Checking if constant {const} is from current file"
      if ← isCurrentFileConstant const then
        result := result.push const
        aesop_trace![zzh_custom] "Adding current file constant to simp: {const}"
    return result

/-- 将当前文件定义的常量添加到 simp 上下文中 -/
private def addCurrentFileConstantsToSimp (ctx : Simp.Context) (goal : MVarId) :
    MetaM Simp.Context := do
  let constants ← collectCurrentFileConstants goal
  if constants.isEmpty then
    return ctx
  -- 获取 base simp theorems
  let mut simpTheoremsArray := ctx.simpTheorems
  if simpTheoremsArray.isEmpty then
    simpTheoremsArray := #[{}]
  let baseSimpTheorems := simpTheoremsArray[0]!
  -- 添加常量到 simp theorems
  let mut newSimpTheorems := baseSimpTheorems
  for const in constants do
    try
      let info ← getConstInfo const
      let isPropType ← isProp info.type
      -- if isPropType then
      --   aesop_trace![zzh_custom]m!"本地prop：{const}"
      -- else
      --   aesop_trace![zzh_custom]m!"本地非prop：{const}"
      newSimpTheorems ←
        if isPropType then
          newSimpTheorems.addConst const

          -- 设置优先级为900，低于默认的1000
          -- newSimpTheorems.addConst const (inv := true) (post := false) (prio := 900)
        else
          newSimpTheorems.addDeclToUnfold const
    catch _ =>
      pure ()
  -- 更新数组
  simpTheoremsArray := #[newSimpTheorems] ++ simpTheoremsArray[1:]
  return ctx.setSimpTheorems simpTheoremsArray

def normSimpCore (goal : MVarId) (goalMVars : Std.HashSet MVarId) :
    NormM (Option NormRuleResult) := do
  let ctx := (← read).normSimpContext
  goal.withContext do
    let preState ← show MetaM _ from saveState
    let localRules := (← read).ruleSet.localNormSimpRules
    -- 添加当前文件常量到 simp 上下文
    let ctxWithCurrentFile ← addCurrentFileConstantsToSimp ctx.toContext goal

    -- 记录实际使用的方法
    let mut actuallyUsedSimpAll := ctx.useHyps

    let result ←
      if ctx.useHyps then
        -- 先尝试 simp_all（用 ConfigCtx 构建的 context）
        let resultOpt ← try
          let (ctxAll, simprocsAll) ←
            addLocalRules localRules ctxWithCurrentFile ctx.simprocs
              (isSimpAll := true)
          let resultAll ← Aesop.simpAll goal ctxAll simprocsAll
          -- aesop_trace![zzh_custom] m!"✅ simp_all succeeded"
          pure (some resultAll)
        catch e =>
          aesop_trace![zzh_custom] m!"❌ simp_all failed: {e.toMessageData}"
          pure none

        match resultOpt with
        | some result => pure result
        | none =>
          -- simp_all 失败，用 Simp.Config（而非 ConfigCtx）重新构建 context 并使用 simp at *
          aesop_trace![zzh_custom] m!"Rebuilding context with Simp.Config for simp at * fallback"
          show MetaM _ from restoreState preState  -- 恢复状态
          actuallyUsedSimpAll := false  -- 记录实际用了 simp at *

          -- 用 Simp.Config 重新构建 simp context（关键：不用 ConfigCtx）
          let ruleSet := (← read).ruleSet
          let fallbackCtx ← Simp.mkContext (config := {})
            (simpTheorems := ruleSet.simpTheoremsArray.map (·.snd))
            (congrTheorems := ← getSimpCongrTheorems)
          let fallbackCtxWithFile ← addCurrentFileConstantsToSimp fallbackCtx goal

          let (ctxStar, simprocsStar) ←
            addLocalRules localRules fallbackCtxWithFile ctx.simprocs
              (isSimpAll := false)
          let resultStar ← Aesop.simpGoalWithAllHypotheses goal ctxStar simprocsStar
          aesop_trace![zzh_custom] m!"✅ simp at * completed"
          pure resultStar
      else
        let (ctx, simprocs) ←
          addLocalRules localRules ctxWithCurrentFile ctx.simprocs
            (isSimpAll := false)
        Aesop.simpGoalWithAllHypotheses goal ctx simprocs

    -- It can happen that simp 'solves' the goal but leaves some mvars
    -- unassigned. In this case, we treat the goal as unchanged.
    let result ←
      match result with
      | .solved .. =>
        let anyMVarDropped ← goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)
        if anyMVarDropped then
          -- aesop_trace[steps] "Normalisation simp solved the goal but dropped some metavariables. Skipping normalisation simp."
          show MetaM _ from restoreState preState
          pure .unchanged
        else
          pure result
      | .unchanged .. =>
        aesop_trace[steps] "norm simp left the goal unchanged"
        pure result
      | .simplified .. =>
        pure result

    let postState ← show MetaM _ from saveState
    match result with
    | .unchanged => return none
    | .solved usedTheorems => do
      let step ←
        mkNormSimpScriptStep goal none preState postState usedTheorems actuallyUsedSimpAll
      return some $ .proved #[step]
    | .simplified newGoal usedTheorems => do
      let step ←
        mkNormSimpScriptStep goal newGoal preState postState usedTheorems actuallyUsedSimpAll
      applyDiffToForwardState (← diffGoals goal newGoal)
      return some $ .succeeded newGoal #[step]
where
  addLocalRules (localRules : Array LocalNormSimpRule) (ctx : Simp.Context)
      (simprocs : Simp.SimprocsArray) (isSimpAll : Bool) :
      NormM (Simp.Context × Simp.SimprocsArray) :=
    localRules.foldlM (init := (ctx, simprocs)) λ (ctx, simprocs) r =>
      try
        elabRuleTermForSimpMetaM goal r.simpTheorem ctx simprocs isSimpAll
      catch _ =>
        return (ctx, simprocs)

@[inline, always_inline]
def checkSimp (name : String) (mayCloseGoal : Bool) (goal : MVarId)
    (x : NormM (Option NormRuleResult)) : NormM (Option NormRuleResult) := do
  if ! (← Check.rules.isEnabled) then
    x
  else
    let preMetaState ← show MetaM _ from saveState
    let result? ← x
    let newGoal? := result?.bind (·.newGoal?)
    let postMetaState ← show MetaM _ from saveState
    let introduced :=
        (← getIntroducedExprMVars preMetaState postMetaState).filter
        (some · != newGoal?)
    unless introduced.isEmpty do throwError
        "{Check.rules.name}: {name} introduced mvars:{introduced.map (·.name)}"
    let assigned :=
        (← getAssignedExprMVars preMetaState postMetaState).filter (· != goal)
    unless assigned.isEmpty do throwError
        "{Check.rules.name}: {name} assigned mvars:{introduced.map (·.name)}"
    if ← pure (! mayCloseGoal && newGoal?.isNone) <&&> goal.isAssigned then
        throwError "{Check.rules.name}: {name} solved the goal"
    return result?

def normSimp (goal : MVarId) (goalMVars : Std.HashSet MVarId) :
    NormM (Option NormRuleResult) := do
  profilingRule .normSimp (wasSuccessful := λ _ => true) do
    checkSimp "norm simp" (mayCloseGoal := true) goal do
      withNormTraceNode .normSimp do
        try
          normSimpCore goal goalMVars
        catch e =>
          throwError "aesop: error in norm simp: {e.toMessageData}"

def normUnfoldCore (goal : MVarId) : NormM (Option NormRuleResult) := do
  let unfoldRules := (← read).ruleSet.unfoldRules
  let (result, steps) ← unfoldManyStarS goal (unfoldRules.find? ·) |>.run
  match result with
  | none =>
    aesop_trace[steps] "nothing to unfold"
    return none
  | some newGoal =>
    applyDiffToForwardState (← diffGoals goal newGoal)
    return some $ .succeeded newGoal steps

def normUnfold (goal : MVarId) : NormM (Option NormRuleResult) := do
  profilingRule .normUnfold (wasSuccessful := λ _ => true) do
    checkSimp "unfold simp" (mayCloseGoal := false) goal do
      withNormTraceNode .normUnfold do
        try
          normUnfoldCore goal
        catch e =>
          throwError "aesop: error in norm unfold: {e.toMessageData}"

inductive NormSeqResult where
  | proved (script : Array (DisplayRuleName × Option (Array Script.LazyStep)))
  | changed (goal : MVarId)
      (script : Array (DisplayRuleName × Option (Array Script.LazyStep)))
  | unchanged

def NormRuleResult.toNormSeqResult (ruleName : DisplayRuleName) :
    NormRuleResult → NormSeqResult
  | .proved steps? => .proved #[(ruleName, steps?)]
  | .succeeded goal steps? => .changed goal #[(ruleName, steps?)]

def optNormRuleResultToNormSeqResult :
    Option (DisplayRuleName × NormRuleResult) → NormSeqResult
  | some (ruleName, r) => r.toNormSeqResult ruleName
  | none => .unchanged

abbrev NormStep :=
  MVarId → Array (IndexMatchResult NormRule) →
  Array (IndexMatchResult NormRule) → NormM NormSeqResult

def runNormSteps (goal : MVarId) (steps : Array NormStep)
    (stepsNe : 0 < steps.size) : NormM NormSeqResult := do
  let ctx ← readThe NormM.Context
  let maxIterations := ctx.options.maxNormIterations
  let mut iteration := 0
  let mut step : Fin steps.size := ⟨0, stepsNe⟩
  let mut goal := goal
  let mut scriptSteps := #[]
  let mut preSimpRules := ∅
  let mut postSimpRules := ∅
  let mut anySuccess := false
  while iteration < maxIterations do
    if step.val == 0 then
      let rules ←
        selectNormRules ctx.ruleSet (← getThe NormM.State).forwardRuleMatches
          goal
      let (preSimpRules', postSimpRules') :=
        rules.partition λ r => r.rule.extra.penalty < (0 : Int)
      preSimpRules := preSimpRules'
      postSimpRules := postSimpRules'
    match ← steps[step] goal preSimpRules postSimpRules with
    | .changed newGoal scriptSteps' =>
      anySuccess := true
      goal := newGoal
      scriptSteps := scriptSteps ++ scriptSteps'
      iteration := iteration + 1
      step := ⟨0, stepsNe⟩
    | .proved scriptSteps' =>
      scriptSteps := scriptSteps ++ scriptSteps'
      return .proved scriptSteps
    | .unchanged =>
      if h : step.val + 1 < steps.size then
        step := ⟨step.val + 1, h⟩
      else
        if anySuccess then
          return .changed goal scriptSteps
        else
          return .unchanged
  throwError "aesop: exceeded maximum number of normalisation iterations ({maxIterations}). This means normalisation probably got stuck in an infinite loop."

namespace NormStep

def runPreSimpRules (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, preSimpRules, _ => do
    optNormRuleResultToNormSeqResult <$>
      runFirstNormRule goal mvars preSimpRules

def runPostSimpRules (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, _, postSimpRules =>
    optNormRuleResultToNormSeqResult <$>
      runFirstNormRule goal mvars postSimpRules

def unfold : NormStep
  | goal, _, _ => do
    if ! (← readThe NormM.Context).options.enableUnfold then
      aesop_trace[steps] "norm unfold is disabled (options := \{ ..., enableUnfold := false })"
      return .unchanged
    let r := (← normUnfold goal).map (.normUnfold, ·)
    return optNormRuleResultToNormSeqResult r

def simp (mvars : Std.HashSet MVarId) : NormStep
  | goal, _, _ => do
    if ! (← readThe NormM.Context).normSimpContext.enabled then
      aesop_trace[steps] "norm simp is disabled (simp_options := \{ ..., enabled := false })"
      return .unchanged
    let r := (← normSimp goal mvars).map (.normSimp, ·)
    return optNormRuleResultToNormSeqResult r

end NormStep

partial def normalizeGoalMVar (goal : MVarId)
    (mvars : UnorderedArraySet MVarId) : NormM NormSeqResult := do
  let mvarsHashSet := .ofArray mvars.toArray
  let mut normSteps := #[
    NormStep.runPreSimpRules mvars,
    NormStep.unfold,
    NormStep.simp mvarsHashSet,
    NormStep.runPostSimpRules mvars
  ]
  runNormSteps goal normSteps
    (by simp (config := { decide := true }) [normSteps])

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) [Aesop.Queue Q] :
    SearchM Q Bool := do
  let g ← gref.get
  let preGoal := g.preNormGoal
  if ← g.isRoot then
    -- For the root goal, we skip normalization.
    let rootState ← getRootMetaState
    gref.modify (·.setNormalizationState (.normal preGoal rootState #[]))
    return false
  match g.normalizationState with
  | .provenByNormalization .. => return true
  | .normal .. => return false
  | .notNormal => pure ()
  let normCtx := { (← read) with }
  let normState := {
    forwardState := g.forwardState
    forwardRuleMatches := g.forwardRuleMatches
  }
  let ((normResult, { forwardState, forwardRuleMatches }), postState) ←
    g.runMetaMInParentState do
      normalizeGoalMVar preGoal g.mvars |>.run normCtx |>.run normState
  match normResult with
  | .changed postGoal script? =>
    gref.modify λ g =>
      g.setNormalizationState (.normal postGoal postState script?)
        |>.setForwardState forwardState
        |>.setForwardRuleMatches forwardRuleMatches
    return false
  | .unchanged =>
    gref.modify (·.setNormalizationState (.normal preGoal postState #[]))
    return false
  | .proved script? =>
    gref.modify
      (·.setNormalizationState (.provenByNormalization postState script?))
    gref.markProvenByNormalization
    return true

end Aesop
