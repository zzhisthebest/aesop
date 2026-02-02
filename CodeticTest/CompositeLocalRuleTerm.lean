/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

-- Composite terms are supported by the `apply` and `forward` builders...

structure A where

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example (h : A → β → γ) (b : β) : γ := by
  codetic

example (h : A → β → γ) (b : β) : γ := by
  codetic (add safe apply (h {}))

example (h : A → β → γ) (b : β) : γ := by
  codetic (add safe forward (h {}))

-- ... and also by the `simp` builder.

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example {P : α → Prop} (h : A → x = y) (p : P x) : P y := by
  codetic

example {P : α → Prop} (h : A → x = y) (p : P x) : P y := by
  codetic (add simp (h {}))

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example {P : α → Prop} (h₁ : A → x = y) (h₂ : A → y = z) (p : P x) : P z := by
  codetic

example {P : α → Prop} (h₁ : A → x = y) (h₂ : A → y = z) (p : P x) : P z := by
  codetic (add simp [(h₁ {}), (h₂ {})])
