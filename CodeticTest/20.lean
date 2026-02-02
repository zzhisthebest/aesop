/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Codetic

set_option codetic.check.all true

attribute [codetic safe cases (cases_patterns := [List.Mem _ []])] List.Mem
attribute [codetic unsafe 50% constructors] List.Mem
attribute [codetic unsafe 50% cases (cases_patterns := [List.Mem _ (_ :: _)])] List.Mem

@[codetic safe [constructors, cases (cases_patterns := [All _ [], All _ (_ :: _)])]]
inductive All (P : α → Prop) : List α → Prop where
  | none : All P []
  | more {x xs} : P x → All P xs → All P (x :: xs)

@[simp]
theorem All.cons (P : α → Prop) (x : α) (xs : List α)
  : All P (x :: xs) ↔ (P x ∧ All P xs) := by
  codetic

theorem mem (P : α → Prop) (xs : List α)
  : All P xs ↔ ∀ a : α, a ∈ xs → P a := by
  induction xs
  case nil => codetic
  case cons x xs ih => codetic (config := { useSimpAll := false })

theorem mem' (P : α → Prop) (xs : List α)
  : All P xs ↔ ∀ a : α, a ∈ xs → P a := by
  induction xs <;> codetic
