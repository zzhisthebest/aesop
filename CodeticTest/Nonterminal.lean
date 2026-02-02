/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

structure MyTrue₁
structure MyTrue₂

@[codetic safe]
structure MyTrue₃ where
  tt : MyTrue₁

/--
warning: codetic: failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : MyTrue₃ := by
  codetic
  apply MyTrue₁.mk

@[codetic safe]
structure MyFalse where
  falso : False

/--
warning: codetic: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : MyFalse := by
  codetic

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : MyFalse := by
  codetic (config := { terminal := true })

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : MyFalse := by
  codetic (config := { warnOnNonterminal := false })

@[codetic safe]
structure MyFalse₂ where
  falso : False
  tt : MyTrue₃

/--
warning: codetic: failed to prove the goal after exhaustive search.
---
error: unsolved goals
case falso
⊢ False

case tt
⊢ MyTrue₁
-/
#guard_msgs in
example : MyFalse₂ := by
  codetic

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
set_option codetic.warn.nonterminal false in
example : MyFalse := by
  codetic

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
set_option codetic.warn.nonterminal true in
example : MyFalse := by
  codetic (config := { warnOnNonterminal := false })
