/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public meta import Codetic.RuleTac.Basic
public meta import Codetic.Frontend.Attribute
public meta import Lean.Meta.Tactic.LibrarySearch
public meta import Lean.PrettyPrinter

public section

open Lean
open Lean.Meta
open Lean.Meta.LibrarySearch
open Lean.Elab.Tactic (evalTactic)
open Lean.PrettyPrinter (delab)

namespace Codetic.BuiltinRules

/--
Apply? rule: get the first tactic that `apply?` would recommend (via library search),
then run that tactic (e.g. `exact Foo.bar` or `apply Foo.bar`). Success probability 75%.
-/
@[codetic unsafe 80% tactic (rule_sets := [codetic_builtin])]
meta def applyQuestion : RuleTac :=
  RuleTac.ofTacticSyntax λ input => do
    codetic_trace![zzh_custom] m!"🔍 applyQuestion rule called for goal {input.goal}"
    let preState ← saveState
    -- Use librarySearch to get suggestions, then take the first one
    -- tactic returns goals unchanged so we get partial results
    let tactic := fun (_ : Bool) (g : List MVarId) => pure g
    -- Call librarySearch - it may return none (complete solution) or some (partial results)
    codetic_trace![zzh_custom] m!"🔍 Calling librarySearch..."
    let result? ← try
        librarySearch input.goal tactic (allowFailure := fun _ => pure true)
      catch e =>
        codetic_trace![zzh_custom] m!"❌ librarySearch threw exception: {e.toMessageData}"
        preState.restore
        failure
    match result? with
    | none => codetic_trace![zzh_custom] m!"🔍 librarySearch returned: none (complete solution)"
    | some results => codetic_trace![zzh_custom] m!"🔍 librarySearch returned: some ({results.size} results)"
    match result? with
    | none =>
      -- Complete solution found; librarySearch already closed the goal
      codetic_trace![zzh_custom] m!"✅ Complete solution found!"
      -- Check if goal is still declared (might be closed)
      let goalStillExists ← input.goal.isDeclared
      codetic_trace![zzh_custom] m!"🔍 Goal still exists: {goalStillExists}"
      if goalStillExists then
        let some proofExpr ← getExprMVarAssignment? input.goal | do
          codetic_trace![zzh_custom] m!"❌ Goal exists but no assignment found"
          preState.restore
          failure
        codetic_trace![zzh_custom] m!"🔍 Proof expr: {proofExpr}"
        let stx ← input.goal.withContext (delab proofExpr)
        codetic_trace![zzh_custom] m!"🔍 Delabed tactic: {stx}"
        preState.restore
        `(tactic| exact $stx)
      else
        -- Goal is closed, we need to reconstruct the proof
        codetic_trace![zzh_custom] m!"🔍 Goal is closed, reconstructing proof..."
        preState.restore
        -- Re-run librarySearch but this time we'll get the proof before it closes
        -- Use a tactic that doesn't close the goal but captures the proof
        let captureProof := fun (_ : Bool) (g : List MVarId) => do
          -- Try to get proof before returning
          let some proof ← getExprMVarAssignment? input.goal | pure g
          codetic_trace![zzh_custom] m!"🔍 Captured proof in tactic: {proof}"
          pure g  -- Return goals unchanged so we get partial result
        let result? ← librarySearch input.goal captureProof (allowFailure := fun _ => pure true)
        match result? with
        | some results =>
          if h : 0 < results.size then
            let (_remaining, mctx) := results[0]'h
            setMCtx mctx
            let some proofExpr ← getExprMVarAssignment? input.goal | do
              codetic_trace![zzh_custom] m!"❌ No proof in mctx"
              failure
            let stx ← input.goal.withContext (delab proofExpr)
            codetic_trace![zzh_custom] m!"🔍 Delabed tactic: {stx}"
            `(tactic| exact $stx)
          else
            failure
        | none => failure
    | some results =>
      codetic_trace![zzh_custom] m!"🔍 Got {results.size} partial results"
      if h : 0 < results.size then
        let (_remaining, mctx) := results[0]'h
        codetic_trace![zzh_custom] m!"🔍 Using first result, remaining goals: {_remaining.length}"
        -- Work in the mctx where the proof was found
        setMCtx mctx
        let some proofExpr ← getExprMVarAssignment? input.goal | do
          codetic_trace![zzh_custom] m!"❌ No proof assignment found in mctx"
          preState.restore
          failure
        codetic_trace![zzh_custom] m!"🔍 Proof expr: {proofExpr}, hasExprMVar: {proofExpr.hasExprMVar}"
        -- Delab in the correct context before restoring
        let tacStx ← if proofExpr.hasExprMVar then
          let head := proofExpr.getAppFn
          codetic_trace![zzh_custom] m!"🔍 Using apply, head: {head}"
          let headStx ← input.goal.withContext (delab head)
          `(tactic| apply $headStx)
        else
          let stx ← input.goal.withContext (delab proofExpr)
          codetic_trace![zzh_custom] m!"🔍 Using exact, tactic: {stx}"
          `(tactic| exact $stx)
        preState.restore
        return tacStx
      else
        codetic_trace![zzh_custom] m!"❌ librarySearch returned empty results array"
        preState.restore
        failure

end Codetic.BuiltinRules
