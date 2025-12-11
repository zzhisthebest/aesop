/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Builder.Basic
import Aesop.RuleTac.ElabRuleTerm
import Batteries.Lean.Expr
import Lean.Meta.MatchUtil
import Aesop.Tracing

public section

open Lean
open Lean.Meta

namespace Aesop

namespace RuleBuilderOptions

def applyTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.transparency?.getD .default

def applyIndexTransparency (opts : RuleBuilderOptions) : TransparencyMode :=
  opts.indexTransparency?.getD .reducible

end RuleBuilderOptions

namespace RuleBuilder

def getApplyIndexingMode (indexMd : TransparencyMode) (type : Expr) :
    MetaM IndexingMode :=
  if indexMd != .reducible then
    return .unindexed
  else
    IndexingMode.targetMatchingConclusion type

--己。这个函数不返回任何值，只产生警告。
def checkNoIff (type : Expr) : MetaM Unit := do
  if aesop.warn.applyIff.get (← getOptions) then
    forallTelescope type λ _ conclusion => do
      if ← testHelper conclusion λ e => return e.isAppOf' ``Iff then
        logWarning m!"Apply builder was used for a theorem with conclusion A ↔ B.\nYou probably want to use the simp builder or create an alias that applies the theorem in one direction.\nUse `set_option aesop.warn.applyIff false` to disable this warning."
--己。还是在调用别的函数
def applyCore (t : ElabRuleTerm) (pat? : Option RulePattern)
    (imode? : Option IndexingMode) (md indexMd : TransparencyMode)
    (phase : PhaseSpec) : MetaM LocalRuleSetMember := do
  let e ← t.expr
  let type ← inferType e
  let imode ← imode?.getDM $ getApplyIndexingMode indexMd type
  let tac := .apply t.toRuleTerm md--核心代码
  return .global $ .base $ phase.toRule (← t.name) .apply t.scope tac imode pat?

--己。
def apply : RuleBuilder := λ input => do
  --aesop_trace![zzh_custom] "apply的input.term:{input.term}"--例如：Nat.le_trans
  let opts := input.options
  let e ← elabRuleTermForApplyLike input.term
  --aesop_trace![zzh_custom] "apply的e: {e}"--例如：@Nat.le_trans
  let t := ElabRuleTerm.ofElaboratedTerm input.term e
  let type ← inferType e
  checkNoIff type
  --把表达式转为rule pattern
  let pat? ← opts.pattern?.mapM (RulePattern.elab · e)
  applyCore t pat? opts.indexingMode? opts.applyTransparency
    opts.applyIndexTransparency input.phase

end Aesop.RuleBuilder
