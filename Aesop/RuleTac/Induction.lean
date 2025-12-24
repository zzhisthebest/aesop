/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Aesop.RuleTac.Basic
public import Aesop.Script.CtorNames
public import Aesop.Script.ScriptM
import Aesop.Script.SpecificTactics
import Aesop.Util.Unfold
import Lean.Meta.Tactic.Induction
import Aesop.Tracing
public section

open Lean
open Lean.Meta

namespace Aesop

namespace RuleTac

/-- Get the recursor name for an inductive type. -/
def getRecursorName (decl : Name) : MetaM Name := do
  let recOnName := decl ++ `recOn
  if (← getEnv).contains recOnName then
    return recOnName
  else
    throwError "Could not find recursor {recOnName} for {decl}"

/-- 判断常量是否属于当前命名空间 -/
def isCurrentNamespaceConstant (constName : Name) : MetaM Bool := do
  let currentNs ← getCurrNamespace
  return currentNs.isPrefixOf constName



/-- 在归纳之后，对目标和指定的 hypotheses 中出现的本地递归定义做一次 unfold（ScriptM 版本，生成 script）。
    递归性通过 `getUnfoldEqnFor?` 检测（有 unfold 等式就视为递归）。-/
--己。
def unfoldRecursiveDefsInTargetS (goal : MVarId) (hypsToUnfold : Array FVarId) : ScriptM MVarId := do
  goal.withContext do
    -- 从 target 和要 unfold 的 hypotheses 中收集所有常量
    let mut constants : Std.HashSet Name := {}

    -- 从 target 收集
    let tgt ← instantiateMVars (← goal.getType)
    constants := tgt.foldConsts (init := constants) (fun c acc => acc.insert c)

    -- 从 hypotheses 收集
    for fvarId in hypsToUnfold do
      if let some ldecl := (← getLCtx).find? fvarId then
        let hypType ← instantiateMVars ldecl.type
        constants := hypType.foldConsts (init := constants) (fun c acc => acc.insert c)

    let currentNs ← getCurrNamespace
    -- 收集当前命名空间下、在目标中出现的递归定义
    let mut recursiveDefs : Array (Name × Option Name) := #[]
    for const in constants do
      if currentNs.isPrefixOf const then
        let unfoldThm? ← getUnfoldEqnFor? const
        if unfoldThm?.isSome then
          recursiveDefs := recursiveDefs.push (const, unfoldThm?)
          aesop_trace![zzh_custom] m!"Found recursive: {const}"

    if recursiveDefs.isEmpty then
      aesop_trace![zzh_custom] m!"No recursive defs to unfold"
      return goal

    -- 构造 unfold 函数
    let unfold? (decl : Name) : Option (Option Name) :=
      match recursiveDefs.find? (fun p => p.fst == decl) with
      | some (_, unfoldThm?) => some unfoldThm?
      | none                 => none

    -- 先在 target 上 unfold
    let mut currentGoal := goal
    if let some (unfoldedGoal, _usedDecls) ← unfoldManyTargetS unfold? currentGoal then
      currentGoal := unfoldedGoal
      -- -- dbg_trace "zzh_custom: Unfolded in target"

    -- 然后在指定的 hypotheses 上 unfold
    for fvarId in hypsToUnfold do
      if let some (unfoldedGoal, _usedDecls) ← unfoldManyAtS unfold? currentGoal fvarId then
        currentGoal := unfoldedGoal
        aesop_trace![zzh_custom] m!"Unfolded in hyp"
        -- -- dbg_trace "Unfolded in hyp "

    return currentGoal

-- 原来的通用 induction（已被 inductionOnVar 替代）
/-
def induction (target : CasesTarget) (md : TransparencyMode)
    (_isRecursiveType : Bool) (ctorNames : Array CtorNames) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let declName ← match target with
      | .decl d => pure d
      | .patterns _ => throwError "induction builder: patterns not supported yet"

    -- -- dbg_trace "zzh_custom: induction rule called for {declName}"

    -- Find first hypothesis matching the inductive type
    -- Filter out variables introduced by previous inductions (from input.inductionIntroducedVars)
    let some hyp ← findHyp declName md input.goal input.inductionIntroducedVars
      | do
        -- -- dbg_trace "zzh_custom: No hypothesis of type {declName} found"
        throwError "No hypothesis of type {declName} found for induction"

    -- -- dbg_trace "zzh_custom: Found hypothesis for {declName}"
    aesop_trace![zzh_custom] m!"zzh_custom: Trying induction {← hyp.getUserName}"
    -- Get recursor name
    let recursorName ← getRecursorName declName

    -- Get FVarIds and names of variables that existed in the original goal before induction
    let (originalFVarIds, originalVarNames) ← input.goal.withContext do
      let mut fvarIds : Std.HashSet FVarId := {}
      let mut names : Std.HashSet Name := {}
      for ldecl in (← getLCtx) do
        if ! ldecl.isImplementationDetail then
          fvarIds := fvarIds.insert ldecl.fvarId
          names := names.insert ldecl.userName
      return (fvarIds, names)

    -- Perform induction using ScriptM, then unfold in ScriptM
    let (some subgoals, steps) ← (do
      -- 先执行归纳
      let some subgoals ← tryInductionS input.goal hyp ctorNames recursorName
        | return none
      aesop_trace![zzh_custom] m!"Induction on { ← hyp.getUserName} succeeded✅"

      -- 在 ScriptM 里对每个子目标做 unfold（会生成 script steps）
      let subgoals ← subgoals.mapM fun (isg : InductionSubgoal) => do
        -- 从子 goal 的所有 hypotheses 中找出原始的（至少名字或FVarId有一个是原来的）
        let hypsToUnfold ← isg.mvarId.withContext do
          let mut vars : Array FVarId := #[]
          for ldecl in (← getLCtx) do
            if ldecl.isImplementationDetail then
              continue
            let fvarId := ldecl.fvarId
            let varName := ldecl.userName

            let isNewFVarId := ! originalFVarIds.contains fvarId
            let isNewName := ! originalVarNames.contains varName
            -- 只有当 FVarId 和名字都是新的时候，才是完全新的变量（如 ih）
            -- 否则，至少有一个是老的，应该 unfold
            if !(isNewFVarId && isNewName) then
              vars := vars.push fvarId
              aesop_trace![zzh_custom] "Will unfold in {varName}"
          return vars
        let unfoldedGoal ← unfoldRecursiveDefsInTargetS isg.mvarId hypsToUnfold
        return ({ isg with mvarId := unfoldedGoal } : InductionSubgoal)

      return some subgoals
    ).run
      | do
        -- dbg_trace "zzh_custom: Induction failed"
        throwError "Induction failed"



    -- Convert InductionSubgoal to Subgoal
    -- Mark only variables that are truly newly introduced by induction
    -- A variable is considered induction-introduced if:
    -- 1. Its FVarId is NOT in the original goal (truly new, not re-introduced)
    -- 2. OR its name is NOT in the original goal (new name, even if same FVarId)
    let goals ← subgoals.mapM λ isg => do
      let diff ← diffGoals input.goal isg.mvarId
      let varsToAdd ← isg.mvarId.withContext do
        let mut vars : Array FVarId := #[]
        for fvarId in diff.addedFVars do
          if let some ldecl := (← getLCtx).find? fvarId then
            let varName := ldecl.userName
            -- Check if this is truly a new variable:
            -- 1. FVarId not in original goal (truly new variable)
            -- 2. AND name not in original goal (not a re-introduced original variable)
            let isNewFVarId := ! originalFVarIds.contains fvarId
            let isNewName := ! originalVarNames.contains varName

            if isNewFVarId && isNewName then
              -- This is a truly new variable introduced by induction
              vars := vars.push fvarId
              -- aesop_trace![zzh_custom] "Marking {varName} as introduced by induction (new FVarId and new name)"
            -- else if isNewFVarId then
            --   -- FVarId is new but name exists - might be a re-introduced variable, skip it
            --   aesop_trace![zzh_custom] "zzh_custom: Not marking {varName} (new FVarId but name exists in original)"
            -- else if isNewName then
            --   -- Name is new but FVarId exists - might be renamed original variable, skip it
            --   aesop_trace![zzh_custom] "zzh_custom: Not marking {varName} (new name but FVarId exists in original)"
            -- else
            --   -- Both exist - definitely not new
            --   aesop_trace![zzh_custom] "zzh_custom: Not marking {varName} (both FVarId and name exist in original)"
        return vars



      let mut newVars : Std.HashSet FVarId := input.inductionIntroducedVars---- 继承父目标的
      for fvarId in varsToAdd do
        newVars := newVars.insert fvarId--加上自己引入的
      return {
        diff
        inductionIntroducedVars := newVars--这样就一代代积累和传下去inductionIntroducedVars，但是有时候一个变量的FVarId会改变，导致后代induction时过滤失败。
      }

    return (goals, some steps, none)
  where
    findHyp (declName : Name) (md : TransparencyMode) (goal : MVarId)
        (excludedVars : Std.HashSet FVarId) : MetaM (Option FVarId) :=
      withTransparency md do goal.withContext do
        let declType ← mkConstWithFreshMVarLevels declName
        (← getLCtx).findDeclM? λ ldecl => do
          if ldecl.isImplementationDetail then
            return none
          else if excludedVars.contains ldecl.fvarId then
            -- Skip variables introduced by previous inductions
            dbg_trace "zzh_custom: Skipping hypothesis {ldecl.userName} (introduced by induction)"
            return none
          else
            -- Check if the hypothesis type is an application of the inductive type
            -- Use isAppOfUpToDefeq like Cases does
            if ← isAppOfUpToDefeq declType ldecl.type then
              dbg_trace "zzh_custom: Hypothesis {ldecl.userName} matches {declName}"
              return some ldecl.fvarId
            else
              return none
-/

namespace Induction

/-- Create a custom induction RuleTac for a specific variable (FVarId). -/
def inductionOnSpecificVar (targetFVarId : FVarId) (declName : Name)
    (ctorNames : Array CtorNames) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    -- Check if the target variable still exists in this goal
    let some ldecl := (← input.goal.withContext getLCtx).find? targetFVarId
      | throwError "Target variable for induction not found"

    aesop_trace![zzh_custom] m!"zzh_custom: Trying induction on specific var {ldecl.userName}"

    -- Get FVarIds and names of variables that existed in the original goal before induction
    let (originalFVarIds, originalVarNames) ← input.goal.withContext do
      let mut fvarIds : Std.HashSet FVarId := {}
      let mut names : Std.HashSet Name := {}
      for ldecl in (← getLCtx) do
        if ! ldecl.isImplementationDetail then
          fvarIds := fvarIds.insert ldecl.fvarId
          names := names.insert ldecl.userName
      return (fvarIds, names)

    -- Get recursor name
    let recursorName ← getRecursorName declName

    -- Perform induction using ScriptM, then unfold in ScriptM
    let (some subgoals, steps) ← (do
      -- 先执行归纳
      let some subgoals ← tryInductionS input.goal targetFVarId ctorNames recursorName
        | return none
      aesop_trace![zzh_custom] m!"Induction on {ldecl.userName} succeeded✅"

      -- 在 ScriptM 里对每个子目标做 unfold（会生成 script steps）
      let subgoals ← subgoals.mapM fun (isg : InductionSubgoal) => do
        -- 从子 goal 的所有 hypotheses 中找出原始的（至少名字或FVarId有一个是原来的）
        let hypsToUnfold ← isg.mvarId.withContext do
          let mut vars : Array FVarId := #[]
          for ldecl in (← getLCtx) do
            if ldecl.isImplementationDetail then
              continue
            let fvarId := ldecl.fvarId
            let varName := ldecl.userName

            let isNewFVarId := ! originalFVarIds.contains fvarId
            let isNewName := ! originalVarNames.contains varName
            -- 只有当 FVarId 和名字都是新的时候，才是完全新的变量（如 ih）
            -- 否则，至少有一个是老的，应该 unfold
            if !(isNewFVarId && isNewName) then
              vars := vars.push fvarId
              aesop_trace![zzh_custom] "Will unfold in {varName}"
          return vars
        let unfoldedGoal ← unfoldRecursiveDefsInTargetS isg.mvarId hypsToUnfold
        return ({ isg with mvarId := unfoldedGoal } : InductionSubgoal)

      return some subgoals
    ).run
      | do
        throwError "Induction failed"

    -- Convert InductionSubgoal to Subgoal
    let goals ← subgoals.mapM λ isg => do
      let diff ← diffGoals input.goal isg.mvarId
      let varsToAdd ← isg.mvarId.withContext do
        let mut vars : Array FVarId := #[]
        for fvarId in diff.addedFVars do
          if let some ldecl := (← getLCtx).find? fvarId then
            let varName := ldecl.userName
            let isNewFVarId := ! originalFVarIds.contains fvarId
            let isNewName := ! originalVarNames.contains varName

            if isNewFVarId && isNewName then
              vars := vars.push fvarId
        return vars

      let mut newVars : Std.HashSet FVarId := input.inductionIntroducedVars
      for fvarId in varsToAdd do
        newVars := newVars.insert fvarId
      return {
        diff
        inductionIntroducedVars := newVars
      }

    return (goals, some steps, none)

end Induction

end Aesop.RuleTac
