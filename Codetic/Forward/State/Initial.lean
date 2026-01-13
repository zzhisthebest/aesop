/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Codetic.Forward.State
public import Codetic.RuleSet
import Codetic.RPINF

public section

open Lean Lean.Meta

namespace Codetic.LocalRuleSet

def mkInitialForwardState (goal : MVarId) (rs : LocalRuleSet) :
    BaseM (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    if ! codetic.dev.statefulForward.get (← getOptions) then
      -- We still initialise the hyp types since these are also used by
      -- stateless forward reasoning.
      let mut hypTypes := ∅
      for ldecl in ← getLCtx do
        if ! ldecl.isImplementationDetail then
          hypTypes := hypTypes.insert (← rpinf ldecl.type)
      return ({ (∅ : ForwardState) with hypTypes }, #[])
    let mut fs : ForwardState := ∅
    let mut ruleMatches := rs.constForwardRuleMatches
    codetic_trace[forward] do
      for m in ruleMatches do
        codetic_trace![forward] "match for constant rule {m.rule.name}"
    for ldecl in ← show MetaM _ from getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let rules ← rs.applicableForwardRules ldecl.type
      let patInsts ← rs.forwardRulePatternSubstsInLocalDecl ldecl
      let (fs', ruleMatches') ←
        fs.addHypWithPatSubstsCore ruleMatches goal ldecl.fvarId rules patInsts
      fs := fs'
      ruleMatches := ruleMatches'
    let patInsts ← rs.forwardRulePatternSubstsInExpr (← goal.getType)
    fs.addPatSubstsCore ruleMatches goal patInsts

end Codetic.LocalRuleSet
