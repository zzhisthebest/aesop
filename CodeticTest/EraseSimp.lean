/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

example (n : Nat) : n + m = m + n := by
  codetic (add simp Nat.add_comm)

attribute [local simp] Nat.add_comm

example (n : Nat) : n + m = m + n := by
  codetic

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  codetic (erase Nat.add_comm) (config := { warnOnNonterminal := false })

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  codetic (erase norm simp Nat.add_comm) (config := { warnOnNonterminal := false })

/--
error: codetic: 'Nat.add_comm' is not registered (with the given features) in any rule set.
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  codetic (erase apply Nat.add_comm)
