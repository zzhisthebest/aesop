/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

@[codetic safe constructors]
structure Sig (α : Sort u) (β : α → Sort v) : Sort _ where
  fst : α
  snd : β fst

def T α β := α ∧ β

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T α β) : Sig α (λ _ => β) := by
  codetic (config := { terminal := true })

example (h : T α β) : Sig α (λ _ => β) := by
  codetic (config := { destructProductsTransparency := .default })

def U := T

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : U α β) : Sig α (λ _ => β) := by
  codetic (config := { terminal := true })

example (h : U α β) : Sig α (λ _ => β) := by
  codetic (config := { destructProductsTransparency := .default })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : U α β ∧ U γ δ) : Sig α (λ _ => γ) := by
  codetic (config := { terminal := true })

example (h : U α β ∧ U γ δ) : Sig α (λ _ => γ) := by
  codetic (config := { destructProductsTransparency := .default })
