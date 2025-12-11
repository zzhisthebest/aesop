/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Aesop.Builder.Basic
import Aesop.RuleTac.Induction
import Batteries.Lean.Expr

public section

open Lean
open Lean.Meta

namespace Aesop

namespace RuleBuilder

def induction : RuleBuilder := λ input => do
  let opts := input.options
  if input.phase.phase == .norm then throwError
    "aesop: induction builder cannot currently be used for norm rules."
  let md := opts.transparency?.getD .reducible
  let (decl, info) ← elabInductiveRuleIdent .induction input.term md

  -- Only support Nat and List for now
  unless decl == ``Nat || decl == ``List do
    throwError "aesop: induction builder currently only supports Nat and List"

  let ctorNames ← mkCtorNames info
  let tac := .induction (.decl decl) md info.isRec ctorNames
  let indexMd := opts.indexTransparency?.getD .reducible
  let imode ← if indexMd == .reducible then
    IndexingMode.hypsMatchingConst decl
  else
    pure IndexingMode.unindexed
  return .global $ .base $ input.phase.toRule decl .induction .global tac imode none

end Aesop.RuleBuilder
