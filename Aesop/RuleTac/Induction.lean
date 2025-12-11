/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Aesop.RuleTac.Basic
public import Aesop.Script.CtorNames
import Aesop.Script.SpecificTactics
import Lean.Meta.Tactic.Induction

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

def induction (target : CasesTarget) (md : TransparencyMode)
    (_isRecursiveType : Bool) (ctorNames : Array CtorNames) : RuleTac :=
  SingleRuleTac.toRuleTac λ input => do
    let declName ← match target with
      | .decl d => pure d
      | .patterns _ => throwError "induction builder: patterns not supported yet"

    dbg_trace "zzh_custom: induction rule called for {declName}"

    -- Find first hypothesis matching the inductive type
    -- Filter out variables introduced by previous inductions (from input.inductionIntroducedVars)
    let some hyp ← findHyp declName md input.goal input.inductionIntroducedVars
      | do
        dbg_trace "zzh_custom: No hypothesis of type {declName} found"
        throwError "No hypothesis of type {declName} found for induction"

    dbg_trace "zzh_custom: Found hypothesis for {declName}"

    -- Get recursor name
    let recursorName ← getRecursorName declName

    -- Perform induction using ScriptM
    let (some subgoals, steps) ← tryInductionS input.goal hyp ctorNames recursorName |>.run
      | do
        dbg_trace "zzh_custom: Induction failed"
        throwError "Induction failed"

    dbg_trace "zzh_custom: Induction succeeded, got {subgoals.size} subgoals"

    -- Get FVarIds and names of variables that existed in the original goal before induction
    let (originalFVarIds, originalVarNames) ← input.goal.withContext do
      let mut fvarIds : Std.HashSet FVarId := {}
      let mut names : Std.HashSet Name := {}
      for ldecl in (← getLCtx) do
        if ! ldecl.isImplementationDetail then
          fvarIds := fvarIds.insert ldecl.fvarId
          names := names.insert ldecl.userName
      return (fvarIds, names)

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
              dbg_trace "zzh_custom: Marking {varName} as introduced by induction (new FVarId and new name)"
            else if isNewFVarId then
              -- FVarId is new but name exists - might be a re-introduced variable, skip it
              dbg_trace "zzh_custom: Not marking {varName} (new FVarId but name exists in original)"
            else if isNewName then
              -- Name is new but FVarId exists - might be renamed original variable, skip it
              dbg_trace "zzh_custom: Not marking {varName} (new name but FVarId exists in original)"
            else
              -- Both exist - definitely not new
              dbg_trace "zzh_custom: Not marking {varName} (both FVarId and name exist in original)"
        return vars
      let mut newVars : Std.HashSet FVarId := input.inductionIntroducedVars
      for fvarId in varsToAdd do
        newVars := newVars.insert fvarId
      return {
        diff
        inductionIntroducedVars := newVars
      }

    return (goals, steps, none)
  where
    /-- Check if a variable name matches typical induction-introduced variable patterns.
    These are usually simple names like n, n1, n2, ih, ih1, ih2, etc. -/
    isInductionVariableName (name : Name) : Bool :=
      let nameStr := name.toString
      -- Match patterns like: n, n1, n2, ..., ih, ih1, ih2, ...
      if nameStr.length ≤ 4 then
        let restAfterN := nameStr.drop 1
        let restAfterIh := nameStr.drop 2
        (nameStr.startsWith "n" && (nameStr.length == 1 || restAfterN.all Char.isDigit)) ||
        (nameStr.startsWith "ih" && (nameStr.length == 2 || restAfterIh.all Char.isDigit)) ||
        (nameStr.length == 1 && match nameStr.get? 0 with | some c => c.isAlpha | none => false)
      else
        false

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

end Aesop.RuleTac
