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
open Lean.Elab.Tactic (evalTactic withoutRecover)

namespace Aesop

namespace RuleTac

/-- Get the recursor name for an inductive type. -/
def getRecursorName (decl : Name) : MetaM Name := do
  let recOnName := decl ++ `recOn
  if (← getEnv).contains recOnName then
    return recOnName
  else
    throwError "Could not find recursor {recOnName} for {decl}"
--己。
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
          -- aesop_trace![zzh_custom] m!"Found recursive: {const}"

    if recursiveDefs.isEmpty then
      -- aesop_trace![zzh_custom] m!"No recursive defs to unfold"
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
    let mut idx:Nat :=0
    for fvarId in hypsToUnfold do
      if let some (unfoldedGoal, _usedDecls) ← unfoldManyAtS unfold? currentGoal fvarId then
        currentGoal := unfoldedGoal
        aesop_trace![zzh_custom] m!"Unfolded in hyp at idx:{idx}"
      idx:=idx+1
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
--己。
/-- 解析函数归纳定理的参数结构，返回 (固定参数数量, 归纳变量数量) -/
def parseFunctionInductType (inductType : Expr) : MetaM (Nat × Nat) := do
  -- inductType 形如: ∀ (fixed...) (motive : ...) (cases...) (vars...), motive vars...
  -- 通过遍历 forall 绑定，用参数名识别 motive
  let mut motiveIdx : Option Nat := none
  let mut casesEnd : Option Nat := none
  let mut currentIdx := 0
  let mut e := inductType

  -- 遍历所有 forall 绑定
  while e.isForall do
    let varName := e.bindingName!
    let varType := e.bindingDomain!

    -- 识别 motive：参数名是 "motive"
    if varName == `motive then
      motiveIdx := some currentIdx
      -- aesop_trace![zzh_custom] m!"Found motive at index {currentIdx}, name: {varName}"

    -- motive 之后的参数：如果还是函数类型，就是 case；否则就是归纳变量
    if motiveIdx.isSome && casesEnd.isNone then
      if !varType.isForall then
        -- 第一个非函数类型参数，归纳变量开始
        casesEnd := some currentIdx
        -- aesop_trace![zzh_custom] m!"Induction vars start at index {currentIdx}"

    e := e.bindingBody!
    currentIdx := currentIdx + 1

  let finalMotiveIdx := motiveIdx.getD 0
  let finalInductVarsStart := casesEnd.getD currentIdx

  let numFixedVars := finalMotiveIdx
  let numInductVars := currentIdx - finalInductVarsStart

  -- aesop_trace![zzh_custom] m!"motiveIdx:{finalMotiveIdx}, inductVarsStart:{finalInductVarsStart}"
  aesop_trace![zzh_custom] m!"numFixedVars:{numFixedVars}, numInductVars:{numInductVars}"
  return (numFixedVars, numInductVars)

--己。
/-- 从表达式中找到所有本地递归函数调用 -/
def findAllLocalRecursiveCalls (e : Expr) : MetaM (Array (Name × Array Expr)) := do
  let currentNs ← getCurrNamespace
  let env ← getEnv

  -- 收集所有常量
  let constants : Std.HashSet Name := e.foldConsts {} (fun c acc => acc.insert c)

  let mut results : Array (Name × Array Expr) := #[]

  -- 遍历常量查找有 .induct 定理的本地递归函数
  for constName in constants.toArray do
    if currentNs.isPrefixOf constName then
      -- 检查是否是递归函数（有 unfold equation）
      let unfoldThm? ← getUnfoldEqnFor? constName
      if unfoldThm?.isSome then
        -- aesop_trace![zzh_custom] m!"Found local recursive function: {constName}"
        -- 在表达式中查找这个常量的具体调用
        if let some sub := e.find? (fun s =>
          match s.getAppFn with
          | .const name _ => name == constName
          | _ => false
        ) then
          -- aesop_trace![zzh_custom] m!"   Found call with args: {sub.getAppArgs} "
          results := results.push (constName, sub.getAppArgs)

  return results

/-- Create a custom induction RuleTac for a specific variable (FVarId). -/
def inductionOnSpecificVar (targetFVarId : FVarId) (declName : Name)
    (ctorNames : Array CtorNames) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    -- Check if the target variable still exists in this goal
    let some ldecl := (← input.goal.withContext getLCtx).find? targetFVarId
      | throwError "Target variable for induction not found"

    -- aesop_trace![zzh_custom] m!"zzh_custom: Trying induction on specific var {ldecl.userName}"

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
      -- aesop_trace![zzh_custom] m!"Induction on {ldecl.userName} succeeded✅"

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
              -- aesop_trace![zzh_custom] "Will unfold in {varName}"
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

/-- Try function induction in ScriptM, similar to tryInductionS -/
def tryFunctionInductionS (goal : MVarId) (funcName : Name) (numFixed : Nat)
    (numInductVars : Nat) : ScriptM (Option (Array MVarId)) := do
  aesop_trace![zzh_custom] m!"tryFunctionInductionS: funcName={funcName}, numFixed={numFixed}, numInductVars={numInductVars}"
  -- 构造 tactic 并执行
  let stxOpt ← goal.withContext do
    -- 1. 先在 target 中查找函数调用
    let tgt ← instantiateMVars (← goal.getType)
    aesop_trace![zzh_custom] m!"Goal type: {tgt}"
    let callOpt := tgt.find? (fun e =>
      match e.getAppFn with
      | .const name _ => name == funcName
      | _ => false
    )

    -- 2. 如果 target 中没找到，在 hypotheses 中查找
    let call ← match callOpt with
      | some c =>
        aesop_trace![zzh_custom] m!"✅ Found function call in target: {c}"
        pure c
      | none =>
        aesop_trace![zzh_custom] m!"Function {funcName} not found in target, searching in hypotheses..."
        let mut foundCall : Option Expr := none
        for ldecl in (← getLCtx) do
          if ldecl.isImplementationDetail then continue
          let hypType ← instantiateMVars ldecl.type
          let hypCall := hypType.find? (fun e =>
            match e.getAppFn with
            | .const name _ => name == funcName
            | _ => false
          )
          if hypCall.isSome then
            aesop_trace![zzh_custom] m!"✅ Found function call in hypothesis {ldecl.userName}: {hypCall.get!}"
            foundCall := hypCall
            break

        match foundCall with
        | some c => pure c
        | none =>
          aesop_trace![zzh_custom] m!"❌ Function {funcName} not found in goal or hypotheses"
          return none

    aesop_trace![zzh_custom] m!"Using function call: {call}"
    let args := call.getAppArgs

    if args.size < numFixed + numInductVars then
      aesop_trace![zzh_custom] m!"❌ Not enough arguments"
      return none

    let fixedArgs := args.extract 0 numFixed
    let inductArgs := args.extract numFixed args.size

    -- 处理固定参数：如果是 fvar 就用名字，否则用表达式字符串
    let mut fixedStrs : Array String := #[]
    for arg in fixedArgs do
      if arg.isFVar then
        let name ← arg.fvarId!.getUserName
        fixedStrs := fixedStrs.push (toString name)
      else
        -- 对于非 fvar，使用 pretty print
        let argStr := toString (← ppExpr arg)
        fixedStrs := fixedStrs.push argStr
        aesop_trace![zzh_custom] m!"Fixed arg (non-fvar): {argStr}"

    -- 处理归纳参数：可以是任何表达式（不限于 fvar）
    let mut inductStrs : Array String := #[]
    for arg in inductArgs do
      if arg.isFVar then
        let name ← arg.fvarId!.getUserName
        inductStrs := inductStrs.push (toString name)
      else
        -- 对于非 fvar（如 N+1, 0 等），使用 pretty print
        let argStr := toString (← ppExpr arg)
        inductStrs := inductStrs.push argStr
        aesop_trace![zzh_custom] m!"Induct arg (non-fvar): {argStr}"

    -- 动态构造 induction tactic
    let inductIdent := Lean.mkIdent (funcName ++ `induct)
    let inductStr := String.intercalate ", " inductStrs.toList
    let fixedStr := String.intercalate " " fixedStrs.toList
    let tacticStr := s!"induction {inductStr} using {inductIdent.getId} {fixedStr}"

    aesop_trace![zzh_custom] m!"Generated tactic string: {tacticStr}"

    -- 解析 tactic 字符串
    let env ← getEnv
    let parserFn := Parser.runParserCategory env `tactic tacticStr
    match parserFn with
    | Except.ok stx =>
      return some stx
    | Except.error err =>
      aesop_trace![zzh_custom] m!"❌ Tactic Parse error: {err}"
      return none

  let some stx := stxOpt |
    return none

  -- 创建简单的 TacticBuilder
  let tacticBuilder (_ : Array MVarId) : Script.TacticBuilder := do
    -- 将 Syntax 转换为 TSyntax `tactic
    let tacticSyntax : TSyntax `tactic := ⟨stx⟩
    return .unstructured tacticSyntax
  -- 在 ScriptM 中执行 tactic
  withOptScriptStep goal id tacticBuilder do
    show MetaM _ from observing? do
      let postGoalsList ← Lean.Elab.Tactic.run goal (evalTactic stx) |>.run'
      return postGoalsList.toArray

/-- Create a RuleTac that applies function induction for a specific recursive function,
    modeled after inductionOnSpecificVar -/
def functionInductionRule (funcName : Name): RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    -- aesop_trace![zzh_custom] m!"🎯 Applying function induction for {funcName}"
    -- Get .induct theorem info

    let inductName := funcName ++ `induct
    Lean.executeReservedNameAction inductName--.induct是lazy generation的，所以要先use一次。
    let inductConst ← mkConstWithFreshMVarLevels inductName
    let inductType ← inferType inductConst

    -- Parse parameter structure
    let (numFixed, numInductVars) ← parseFunctionInductType inductType


    let (originalFVarIds, originalVarNames) ← input.goal.withContext do
      -- 获取原始变量
      let mut fvarIds : Std.HashSet FVarId := {}
      let mut names : Std.HashSet Name := {}
      for ldecl in (← getLCtx) do
        if ! ldecl.isImplementationDetail then
          fvarIds := fvarIds.insert ldecl.fvarId
          names := names.insert ldecl.userName

      return (fvarIds, names)

    -- 使用 tryFunctionInductionS 执行归纳并 unfold（模仿 inductionOnSpecificVar 的结构）
    let (some subgoals, steps) ← (do
      -- 先执行函数归纳
      let some subgoals ← tryFunctionInductionS input.goal funcName numFixed numInductVars
        | aesop_trace![zzh_custom] m!"❌ tryFunctionInductionS failed"
          return none

      -- 在 ScriptM 里对每个子目标做 unfold（会生成 script steps）
      let subgoals ← subgoals.mapM fun (mvarId : MVarId) => do
        -- 从子 goal 的所有 hypotheses 中找出原始的（至少名字或FVarId有一个是原来的）
        let hypsToUnfold ← (mvarId.withContext do
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
              aesop_trace![zzh_custom] m!"要unfold的hyp: {varName}"
          return vars: MetaM (Array FVarId))
        let unfoldedGoal ← unfoldRecursiveDefsInTargetS mvarId hypsToUnfold
        return unfoldedGoal

      aesop_trace![zzh_custom] m!"函数归纳产生的subgoals: {subgoals}"
      return some subgoals
    ).run
      | throwError "Function induction failed"

    -- 转换为 Subgoal（与 inductionOnSpecificVar 相同）
    let goals ← subgoals.mapM λ mvarId => do
      let sg ← mvarIdToSubgoal input.goal mvarId
      return { sg with functionInductionApplied := input.functionInductionApplied.insert funcName }

    aesop_trace![zzh_custom] m!"Function induction on {funcName} succeeded✅"

    return (goals, some steps, none)

end Induction

end Aesop.RuleTac
