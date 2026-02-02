/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

-- set_option codetic.check.script.steps false

/--
info: Try this:

  [apply]     intro a
    simp_all only [Nat.add_zero]
    sorry
---
warning: codetic: failed to prove the goal after exhaustive search.
---
error: unsolved goals
n : Nat
P : Nat → Prop
a : P n
⊢ P (n + 1)
-/
#guard_msgs in
example {P : Nat → Prop} : P (n + 0) → P (n + 1) := by
  codetic?

inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : Even n → Even (n + 2)

/--
info: Try this:

  [apply]   sorry
---
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example : Even 5 := by
  codetic?

attribute [codetic safe constructors] Even

/--
info: Try this:

  [apply]     apply Even.add_two
    apply Even.add_two
    sorry
---
warning: codetic: failed to prove the goal after exhaustive search.
---
error: unsolved goals
case a.a
⊢ Even 1
-/
#guard_msgs in
example : Even 5 := by
  codetic?
