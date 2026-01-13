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

@[codetic unsafe 50% (rule_sets := [codetic_builtin])]
meta def omega : RuleTac :=
  RuleTac.ofTacticSyntax (fun _ => `(tactic| omega))

end Codetic.BuiltinRules
