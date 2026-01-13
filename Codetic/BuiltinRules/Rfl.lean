/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import Codetic.RuleTac.Basic
import Codetic.Frontend.Attribute

public section

open Lean Lean.Elab.Tactic

namespace Codetic.BuiltinRules

@[codetic safe 0 (rule_sets := [codetic_builtin])]
meta def rfl : RuleTac :=
  RuleTac.ofTacticSyntax λ _ => `(tactic| rfl)

end Codetic.BuiltinRules
