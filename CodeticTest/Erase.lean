/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

@[codetic [10% cases, safe constructors]]
inductive Even : Nat → Prop
  | zero : Even 0
  | plus_two : Even n → Even (n + 2)

example : Even 2 := by
  codetic

-- Removing the Codetic attribute erases all rules associated with the identifier
-- from all rule sets.
attribute [-codetic] Even

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Even 2 := by
  codetic (config := { terminal := true })

example : Even 2 := by
  codetic (add safe Even)

-- We can also selectively remove rules in a certain phase or with a certain
-- builder.
attribute [codetic [unsafe 10% cases, safe constructors]] Even

erase_codetic_rules [ unsafe Even ]

example : Even 2 := by
  codetic

erase_codetic_rules [ constructors Even ]

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Even 2 := by
  codetic (config := { terminal := true })

example : Even 2 := by
  codetic (add safe constructors Even)
