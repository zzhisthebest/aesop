/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

-- This option would make Codetic time out.
set_option codetic.check.all false

inductive Even : Nat → Prop
| zero : Even Nat.zero
| plus_two {n} : Even n → Even (n + 2)

attribute [codetic safe] Even.zero Even.plus_two

example : Even 500 := by
  codetic (config := { maxRuleApplications := 0, maxRuleApplicationDepth := 0 })
