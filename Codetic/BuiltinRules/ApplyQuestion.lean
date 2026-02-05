/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public meta import Codetic.RuleTac.Basic
import Codetic.Frontend.Attribute

public section

open Lean

namespace Codetic.BuiltinRules

/--
Exact? rule: Uses the `exact?` tactic to find a lemma that exactly solves the goal.
This is an unsafe rule that will fail if no exact match is found.
-/
@[codetic unsafe 25% tactic (rule_sets := [codetic_builtin])]
meta def exactQuestion : RuleTac :=
  RuleTac.ofTacticSyntax (fun _ => `(tactic| exact?))

end Codetic.BuiltinRules
