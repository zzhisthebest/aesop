/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Codetic

set_option codetic.check.all true

attribute [codetic unsafe 50% constructors] List.Mem

@[codetic safe [constructors, cases (cases_patterns := [All _ [], All _ (_ :: _)])]]
inductive All (P : α → Prop) : List α → Prop where
  | none : All P []
  | more (x xs) : P x → All P xs → All P (x :: xs)

theorem weaken (P Q : α → Prop) (wk : ∀ x, P x → Q x) (xs : List α) (h : All P xs)
  : All Q xs := by
  induction h <;> codetic

theorem in_self (xs : List α) : All (· ∈ xs) xs := by
  induction xs
  case nil =>
    codetic
  case cons x xs ih =>
    have wk : ∀ a, a ∈ xs → a ∈ x :: xs := by codetic
    have ih' : All (fun a => a ∈ x :: xs) xs := by codetic (add unsafe 1% weaken)
    codetic
