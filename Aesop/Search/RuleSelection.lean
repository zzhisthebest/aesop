/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Tree.RunMetaM
public import Aesop.Search.SearchM
import Aesop.Builder.Induction
import Aesop.RuleTac.Induction
import Aesop.Script.CtorNames
import Aesop.Rule

public section

open Lean
open Lean.Meta

namespace Aesop

variable [Aesop.Queue Q]

/-- Create dynamic induction rules for each Nat/List variable in the goal.
    Returns an array of index match results with induction rules for each variable. -/
--己。
def createDynamicInductionRules (goal : MVarId)
    (inductionIntroducedVars : Std.HashSet FVarId) :
    MetaM (Array (IndexMatchResult UnsafeRule)) := do
  goal.withContext do
    let mut rules : Array (IndexMatchResult UnsafeRule) := #[]
    let mut idx : Int := 0
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      -- Skip variables introduced by previous inductions
      if inductionIntroducedVars.contains ldecl.fvarId then continue

      let varType ← instantiateMVars ldecl.type
      let declName? : Option Name :=
        if varType.isConstOf ``Nat then
          some ``Nat
        else if varType.isAppOf ``List then
          some ``List
        else
          none

      match declName? with
      | none => continue
      | some declName =>
        -- Get constructor names for the inductive type
        let info ← getConstInfoInduct declName
        let ctorNames ← mkCtorNamesForInfo info

        idx:=idx+1
        -- Create induction rule for this specific variable
        let ruleName : RuleName := {
          name := declName ++ Name.mkSimple (toString idx) --++ ldecl.userName
          builder := .induction
          phase := .unsafe
          scope := .global
        }
        let ruleInfo : UnsafeRuleInfo := {
          successProbability := defaultSuccessProbability
        }

        -- Create rule that directly targets this specific fvarId
        let rule : UnsafeRule := {
          name := ruleName
          indexingMode := .unindexed
          pattern? := none
          extra := ruleInfo
          tac := .inductionOnVar ldecl.fvarId declName ctorNames
        }

        let matchResult : IndexMatchResult UnsafeRule := {
          rule := rule
          locations := ∅
          patternSubsts? := none
        }
        rules := rules.push matchResult

        -- aesop_trace![zzh_custom] "{goal} Added dynamic induction rule for variable {ldecl.userName} : {declName}"

    return rules
where
  mkCtorNamesForInfo (info : InductiveVal) : MetaM (Array CtorNames) := do
    let ctorNamesList ← info.ctors.toArray.toList.mapM λ ctorName => do
      let ctorInfo ← getConstInfoCtor ctorName
      -- Check if constructor has implicit arguments
      let hasImplicitArg := ctorInfo.numParams > 0
      -- Generate default argument names: a, a_1, a_2, ...
      let argNames := (List.range ctorInfo.numFields).map (λ i =>
        if i == 0 then `a else Name.mkSimple s!"a_{i}"
      ) |>.toArray
      let cn : CtorNames := {
        ctor := ctorName
        args := argNames
        hasImplicitArg := hasImplicitArg
      }
      return cn
    return ctorNamesList.toArray
--己。
/-- Create dynamic function induction rules for all local recursive function calls in the goal -/
def createDynamicFunctionInductionRules (goal : MVarId)
    (appliedFunctions : Std.HashSet Name) :
    MetaM (Array (IndexMatchResult UnsafeRule)) := do
  goal.withContext do
    -- Find all local recursive function calls with .induct theorems
    -- Check both target and hypotheses (like createDynamicInductionRules)
    let mut allCalls : Std.HashMap Name (Array Expr) := {}

    -- 1. Find calls in target
    let tgt ← instantiateMVars (← goal.getType)
    let targetCalls ← RuleTac.Induction.findAllLocalRecursiveCalls tgt
    for (funcName, callArgs) in targetCalls do
      allCalls := allCalls.insert funcName callArgs

    -- 2. Find calls in hypotheses (模仿 createDynamicInductionRules)
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let hypType ← instantiateMVars ldecl.type
      let hypCalls ← RuleTac.Induction.findAllLocalRecursiveCalls hypType
      for (funcName, callArgs) in hypCalls do
        if !allCalls.contains funcName then
          allCalls := allCalls.insert funcName callArgs

    let mut rules : Array (IndexMatchResult UnsafeRule) := #[]
    let mut idx : Int := 0
    -- Create a rule for each function that hasn't been applied yet
    for (funcName, _callArgs) in allCalls do
      -- Check if we've already applied function induction on this function
      if appliedFunctions.contains funcName then
        aesop_trace![zzh_custom] m!"Skipping function induction for {funcName} (already applied)"
        continue

      let inductName := funcName ++ `induct
      aesop_trace![zzh_custom] m!"Creating rule for {funcName}"
      idx:=idx+1

      -- Create a dynamic rule for function induction
      let ruleName : RuleName := {
        name := inductName ++ Name.mkSimple (toString idx)
        builder := .induction
        phase := .unsafe
        scope := .global
      }
      let ruleInfo : UnsafeRuleInfo := {
        successProbability := ⟨0.75⟩--设置优先级
      }

      let rule : UnsafeRule := {
        name := ruleName
        indexingMode := .unindexed
        pattern? := none
        extra := ruleInfo
        tac := .functionInduction funcName  -- 参数数量在 functionInductionRule 中动态获取
      }

      let matchResult : IndexMatchResult UnsafeRule := {
        rule := rule
        locations := ∅
        patternSubsts? := none
      }

      aesop_trace![zzh_custom] m!"Added dynamic function induction rule for {funcName}"
      rules := rules.push matchResult

    return rules

def selectNormRules (rs : LocalRuleSet) (fms : ForwardRuleMatches)
    (goal : MVarId) : BaseM (Array (IndexMatchResult NormRule)) :=
  profilingRuleSelection do rs.applicableNormalizationRules fms goal

def preprocessRule : SafeRule where
  name := {
    name := `Aesop.BuiltinRule.preprocess
    builder := .tactic
    phase := .safe
    scope := .global
  }
  indexingMode := .unindexed
  pattern? := none
  extra := { penalty := 0, safety := .safe }
  tac := .preprocess

def selectSafeRules (g : Goal) :
    SearchM Q (Array (IndexMatchResult SafeRule)) := do
  profilingRuleSelection do
    if ← g.isRoot then
      return #[{
        rule := preprocessRule
        locations := ∅
        patternSubsts? := none
      }]
    let ruleSet := (← read).ruleSet
    g.runMetaMInPostNormState' λ postNormGoal =>
      ruleSet.applicableSafeRules g.forwardRuleMatches postNormGoal
--己。
def selectUnsafeRules (postponedSafeRules : Array PostponedSafeRule)
    (gref : GoalRef) : SearchM Q UnsafeQueue := do
  profilingRuleSelection do
    let g ← gref.get
    match g.unsafeQueue? with
    | some rules => return rules
    | none => do
      let ruleSet := (← read).ruleSet
      let mut unsafeRules ←
        g.runMetaMInPostNormState' λ postNormGoal =>
          ruleSet.applicableUnsafeRules g.forwardRuleMatches postNormGoal

      -- Dynamically add induction rules for each Nat/List variable in the goal
      let dynamicInductionRules ← g.runMetaMInPostNormState' λ postNormGoal =>
        createDynamicInductionRules postNormGoal g.inductionIntroducedVars
      unsafeRules := unsafeRules ++ dynamicInductionRules

      -- Dynamically add function induction rules for all recursive functions
      let dynamicFunctionInductionRules ←
        g.runMetaMInPostNormState' λ postNormGoal =>
          createDynamicFunctionInductionRules postNormGoal g.functionInductionApplied
      unsafeRules := unsafeRules ++ dynamicFunctionInductionRules

      let unsafeQueue := UnsafeQueue.initial postponedSafeRules unsafeRules
      gref.set $ g.setUnsafeRulesSelected true |>.setUnsafeQueue unsafeQueue
      return unsafeQueue

end Aesop
