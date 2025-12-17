/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public meta import Aesop.RuleTac.Basic
import Aesop.Frontend.Attribute

public section

open Lean

namespace Aesop.BuiltinRules

@[aesop unsafe 50% (rule_sets := [builtin])]
meta def omega : RuleTac :=
  RuleTac.ofTacticSyntax (fun _ => `(tactic| omega))

end Aesop.BuiltinRules

