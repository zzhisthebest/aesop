/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CodeticTest.Persistence0

set_option codetic.check.all true

namespace Codetic

@[codetic 50% constructors (rule_sets := [test_persistence1])]
inductive NatOrBool where
  | ofNat (n : Nat)
  | ofBool (b : Bool)

example (b : Bool) : NatOrBool := by
  codetic (rule_sets := [test_persistence1])

end Codetic
