/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Codetic.Search.Expansion
import Codetic.Exception

public section

open Lean Lean.Meta

namespace Codetic

declare_codetic_exception
  safeExpansionFailedException safeExpansionFailedExceptionId
  isSafeExpansionFailedException

structure SafeExpansionM.State where
  numRapps : Nat := 0

abbrev SafeExpansionM Q [Queue Q] := StateRefT SafeExpansionM.State (SearchM Q)

variable [Queue Q]

private def Goal.isSafeExpanded (g : Goal) : BaseIO Bool :=
  (pure g.unsafeRulesSelected) <||> g.hasSafeRapp

-- Typeclass inference struggles with inferring Q, so we have to lift
-- explicitly.
private def liftSearchM (x : SearchM Q α) : SafeExpansionM Q α :=
  x

mutual
  private partial def expandSafePrefixGoal (gref : GoalRef) :
      SafeExpansionM Q Unit := do
    let g ← gref.get
    if g.state.isProven then
      codetic_trace[steps] "Skipping safe rule expansion of goal {g.id} since it is already proven."
      return
    if ! (← g.isSafeExpanded) then
      codetic_trace[steps] "Applying safe rules to goal {g.id}."
      if ← liftSearchM $ normalizeGoalIfNecessary gref then
          -- Goal was already proved by normalisation.
          return
      let maxRapps := (← read).options.maxSafePrefixRuleApplications
      if maxRapps > 0 && (← getThe SafeExpansionM.State).numRapps > maxRapps then
        throw safeExpansionFailedException
      discard $ liftSearchM $ runFirstSafeRule gref
      modifyThe SafeExpansionM.State λ s =>
        { s with numRapps := s.numRapps + 1 }
    else
      codetic_trace[steps] "Skipping safe rule expansion of goal {g.id} since safe rules have already been applied."
    let g ← gref.get
    if g.state.isProven then
      return
    let safeRapps ← g.safeRapps
    if h₁ : 0 < safeRapps.size then
      if safeRapps.size > 1 then
        throwError "codetic: internal error: goal {g.id} has multiple safe rapps"
      expandFirstPrefixRapp safeRapps[0]

  private partial def expandFirstPrefixRapp (rref : RappRef) :
      SafeExpansionM Q Unit := do
    (← rref.get).children.forM expandSafePrefixMVarCluster

  private partial def expandSafePrefixMVarCluster (cref : MVarClusterRef) :
      SafeExpansionM Q Unit := do
    (← cref.get).goals.forM expandSafePrefixGoal
end

def expandSafePrefix : SearchM Q Bool := do
  codetic_trace[steps] "Expanding safe subtree of the root goal."
  try
    expandSafePrefixGoal (← getRootGoal) |>.run' {}
    return true
  catch e =>
    if isSafeExpansionFailedException e then
      return false
    else
      throw e

end Codetic
