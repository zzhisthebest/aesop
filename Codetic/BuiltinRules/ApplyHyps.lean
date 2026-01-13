/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import Codetic.RuleTac.Basic
public meta import Codetic.Script.SpecificTactics
import Codetic.Frontend.Attribute

public section

namespace Codetic.BuiltinRules

open Lean
open Lean.Meta

meta def applyHyp (hyp : FVarId) (goal : MVarId) (md : TransparencyMode) :
    BaseM RuleApplication := do
  let (goals, #[step]) ← applyS goal (.fvar hyp) none md |>.run
    | throwError "codetic: internal error in applyHyps: multiple steps"
  return {
    goals := goals.map λ mvarId => { diff := .empty goal mvarId }
    postState := step.postState
    scriptSteps? := #[step]
    successProbability? := none
  }

@[codetic unsafe 75% tactic (rule_sets := [codetic_builtin])]
meta def applyHyps : RuleTac := λ input =>
  input.goal.withContext do
    let lctx ← getLCtx
    let md := input.options.applyHypsTransparency
    let mut rapps := Array.mkEmpty lctx.decls.size
    for localDecl in lctx do
      if localDecl.isImplementationDetail then continue
      let initialState ← saveState
      try
        let rapp ← applyHyp localDecl.fvarId input.goal md
        rapps := rapps.push rapp
      catch _ => continue
      finally restoreState initialState
    return ⟨rapps⟩

end Codetic.BuiltinRules
