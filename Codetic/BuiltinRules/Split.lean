/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Jannis Limperg
-/
module

public meta import Codetic.RuleTac.Basic
public import Codetic.Script.ScriptM
public meta import Codetic.Script.SpecificTactics
import Codetic.Frontend.Attribute
import Codetic.Script.SpecificTactics

public section

open Lean
open Lean.Meta

namespace Codetic.BuiltinRules

@[codetic (rule_sets := [codetic_builtin]) safe 100]
meta def splitTarget : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some goals, steps) ← splitTargetS? input.goal |>.run | throwError
    "nothing to split in target"
  let goals ← goals.mapM (mvarIdToSubgoal input.goal ·)
  return (goals, steps, none)

meta def splitHypothesesCore (goal : MVarId) :
    ScriptM (Option (Array MVarId)) :=
  withIncRecDepth do
  let some goals ← splitFirstHypothesisS? goal
    | return none
  let mut subgoals := #[]
  for g in goals do
    if let some subgoals' ← splitHypothesesCore g then
      subgoals := subgoals ++ subgoals'
    else
      subgoals := subgoals.push g
  return subgoals

@[codetic (rule_sets := [codetic_builtin]) safe 1000]
meta def splitHypotheses : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (some goals, steps) ← splitHypothesesCore input.goal |>.run
    | throwError "no splittable hypothesis found"
  let goals ← goals.mapM (mvarIdToSubgoal input.goal ·)
  return (goals, steps, none)

end Codetic.BuiltinRules
