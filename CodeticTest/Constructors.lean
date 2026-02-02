/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

@[codetic safe]
inductive Even : Nat → Type
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)

example : Even 6 := by
  codetic

attribute [-codetic] Even

def T n := Even n

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T 6 := by
  codetic (config := { terminal := true })

example : T 6 := by
  codetic (add safe constructors (transparency! := default) Even)
