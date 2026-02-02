/-
Copyright (c) 2022 Asta H. From. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
-/
import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

attribute [codetic safe cases (cases_patterns := [List.Mem _ []])] List.Mem
attribute [codetic unsafe 50% cases (cases_patterns := [List.Mem _ (_ :: _)])] List.Mem

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
theorem Mem.split [DecidableEq α] (xs : List α) (v : α) (h : v ∈ xs)
  : ∃ l r, xs = l ++ v :: r := by
  induction xs
  case nil =>
    codetic
  case cons x xs ih =>
    have dec : Decidable (x = v) := inferInstance
    cases dec
    case isFalse no =>
      codetic (config := { terminal := true }) (erase Codetic.BuiltinRules.ext)
    case isTrue yes =>
      apply Exists.intro []
      apply Exists.intro xs
      rw [yes]
      rfl
