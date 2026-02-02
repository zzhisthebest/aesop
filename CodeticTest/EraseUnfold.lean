/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jannis Limperg
-/

-- Thanks to Jireh Loreaux for reporting this MWE.

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

@[irreducible]
def foo : Nat := 37

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : foo = 37 := by
  codetic (config := { terminal := true }) (erase Codetic.BuiltinRules.rfl)

example : foo = 37 := by
  unfold foo
  rfl

attribute [codetic norm unfold] foo

example : foo = 37 := by codetic (erase Codetic.BuiltinRules.rfl)

attribute [-codetic] foo

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : foo = 37 := by
  codetic (config := { terminal := true }) (erase Codetic.BuiltinRules.rfl)

example : foo = 37 := by
  unfold foo
  rfl
