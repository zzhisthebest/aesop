/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import Codetic.Frontend.Extension
public meta import Codetic.Frontend.RuleExpr
public import Codetic.Frontend.RuleExpr

public meta section

open Lean
open Lean.Elab

namespace Codetic.Frontend

namespace Parser

declare_syntax_cat Codetic.attr_rules

syntax Codetic.rule_expr : Codetic.attr_rules
syntax "[" Codetic.rule_expr,+,? "]" : Codetic.attr_rules

syntax (name := codetic) "codetic " Codetic.attr_rules : attr

end Parser

structure AttrConfig where
  rules : Array RuleExpr
  deriving Inhabited

namespace AttrConfig

def «elab» (stx : Syntax) : TermElabM AttrConfig :=
  withRef stx do
    match stx with
    | `(attr| codetic $e:Codetic.rule_expr) => do
      let r ← RuleExpr.elab e |>.run $ ← ElabM.Context.forAdditionalGlobalRules
      return { rules := #[r] }
    | `(attr| codetic [ $es:Codetic.rule_expr,* ]) => do
      let ctx ← ElabM.Context.forAdditionalGlobalRules
      let rs ← (es : Array Syntax).mapM λ e => RuleExpr.elab e |>.run ctx
      return { rules := rs }
    | _ => throwUnsupportedSyntax

end AttrConfig


initialize registerBuiltinAttribute {
  name := `codetic
  descr := "Register a declaration as an Codetic rule."
  applicationTime := .afterCompilation
  add := λ decl stx attrKind => withRef stx do
    -- TODO: should be checked in any case where `decl` will be passed to `evalConst`
    --ensureAttrDeclIsMeta `codetic decl attrKind
    let rules ← runTermElabMAsCoreM do
      let config ← AttrConfig.elab stx
      config.rules.flatMapM (·.buildAdditionalGlobalRules decl)
    for (rule, rsNames) in rules do
      for rsName in rsNames do
        addGlobalRule rsName rule attrKind (checkNotExists := true)
  erase := λ decl =>
    let ruleFilter :=
      { name := decl, scope := .global, builders := #[], phases := #[] }
    eraseGlobalRules RuleSetNameFilter.all ruleFilter (checkExists := true)
}

end Codetic.Frontend
