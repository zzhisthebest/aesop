/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example (m n : Nat) : m * n = n * m := by
  codetic

example (m n : Nat) : m * n = n * m := by
  codetic (add safe (by rw [Nat.mul_comm]))

example (m n : Nat) : m * n = n * m := by
  codetic (add safe tactic (by rw [Nat.mul_comm m n]))

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example (m n : Nat) : m * n = n * m := by
  codetic (add safe (by rw [Nat.mul_comm m m]))

example (m n : Nat) : m * n = n * m := by
  codetic (add safe (by apply Nat.mul_comm; done))
