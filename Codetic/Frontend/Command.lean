/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import Codetic.Frontend.Basic
public meta import Codetic.Stats.Report
public meta import Codetic.Frontend.Extension
public meta import Codetic.Frontend.RuleExpr
public import Batteries.Linter.UnreachableTactic
import Codetic.Frontend.Extension
import Codetic.Stats.Report

public meta section

open Lean Lean.Elab Lean.Elab.Command

namespace Codetic.Frontend.Parser

syntax (name := declareRuleSets)
  "declare_codetic_rule_sets " "[" ident,+,? "]"
  (" (" &"default" " := " Codetic.bool_lit ")")? : command

elab_rules : command
  | `(declare_codetic_rule_sets [ $ids:ident,* ]
       $[(default := $dflt?:Codetic.bool_lit)]?) => do
    let rsNames := (ids : Array Ident).map (·.getId)
    let dflt := (← dflt?.mapM (elabBoolLit ·)).getD false
    rsNames.forM checkRuleSetNotDeclared
    elabCommand $ ← `(meta initialize ($(quote rsNames).forM $ declareRuleSetUnchecked (isDefault := $(quote dflt))))

elab (name := addRules)
    attrKind:attrKind "add_codetic_rules " e:Codetic.rule_expr : command => do
  let attrKind :=
    match attrKind with
    | `(Lean.Parser.Term.attrKind| local) => .local
    | `(Lean.Parser.Term.attrKind| scoped) => .scoped
    | _ => .global
  let rules ← liftTermElabM do
    let e ← RuleExpr.elab e |>.run (← ElabM.Context.forAdditionalGlobalRules)
    e.buildAdditionalGlobalRules none
  for (rule, rsNames) in rules do
    for rsName in rsNames do
      addGlobalRule rsName rule attrKind (checkNotExists := true)

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addRules

elab (name := eraseRules)
    "erase_codetic_rules " "[" es:Codetic.rule_expr,* "]" : command => do
  let filters ← Elab.Command.liftTermElabM do
    let ctx ← ElabM.Context.forGlobalErasing
    (es : Array _).mapM λ e => do
      let e ← RuleExpr.elab e |>.run ctx
      e.toGlobalRuleFilters
  for fs in filters do
    for (rsFilter, rFilter) in fs do
      eraseGlobalRules rsFilter rFilter (checkExists := true)

syntax (name := showRules)
  withPosition("#codetic_rules" (colGt ppSpace ident)*) : command

elab_rules : command
  | `(#codetic_rules $ns:ident*) => do
    liftTermElabM do
      let lt := λ (n₁, _) (n₂, _) => n₁.cmp n₂ |>.isLT
      let rss ←
        if ns.isEmpty then
          let rss ← getDeclaredGlobalRuleSets
          pure $ rss.qsort lt
        else
          ns.mapM λ n => return (n.getId, ← getGlobalRuleSet n.getId)
      TraceOption.ruleSet.withEnabled do
        for (name, rs, _) in rss do
          withConstCodeticTraceNode .ruleSet (return m!"Rule set '{name}'") do
            rs.trace .ruleSet

def evalStatsReport? (name : Name) : CoreM (Option StatsReport) := do
  try
    unsafe evalConstCheck StatsReport ``StatsReport name
  catch _ =>
    return none

syntax (name := showStats) withPosition("#codetic_stats " (colGt ident)?) : command

elab_rules : command
  | `(#codetic_stats) => do
    logInfo $ StatsReport.default $ ← getStatsArray
  | `(#codetic_stats $report:ident) => do
    let openDecl := OpenDecl.simple ``Codetic.StatsReport []
    withScope (λ s => { s with openDecls := openDecl :: s.openDecls }) do
      let names ← resolveGlobalConst report
      liftTermElabM do
        for name in names do
          if let some report ← evalStatsReport? name then
            logInfo $ report $ ← getStatsArray
            break
        throwError "'{report}' is not a constant of type 'Codetic.StatsReport'"

end Codetic.Frontend.Parser
