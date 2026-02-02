/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

example (h : False) : α := by
  codetic

def T := False

variable {α : Type}

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  codetic (config := { terminal := true })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  codetic (add safe cases (transparency! := reducible) False)
    (config := { terminal := true })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  codetic (add safe cases (transparency := default) False)
    (config := { terminal := true })

example (h : T) : α := by
  codetic (add safe cases (transparency! := default) False)

def U := T

example (h : U) : α := by
  codetic (add safe cases (transparency! := default) False)
