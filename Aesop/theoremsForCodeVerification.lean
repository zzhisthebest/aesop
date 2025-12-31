/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

import Aesop.Frontend.Attribute

/-!
# Theorems for Code Verification

This file contains simp theorems specifically for code verification tasks.
These theorems are tagged with `@[aesop norm simp]` so they are only used
when `aesop` is called, not by regular `simp`.

## Usage

Import this file and call:
```lean
aesop (options := { useDefaultSimpSet := false })
```

This will use:
- Only the theorems tagged here with `@[aesop norm simp]`
- Local non-recursive definitions (automatically added)
- No default `@[simp]` theorems from Lean/Mathlib
-/

namespace TheoremsForCodeVerification

attribute [simp]
Array.eraseIdx!
Int.mul_neg_of_neg_of_pos
Int.mul_comm
Array.all_iff_forall

-- attribute [aesop safe constructors cases] Array


--以下是为了替换grind
--List的定理
@[simp]
theorem get_take_eq (l : List α) (i n : Nat)
  (h : i < Nat.min l.length n) :
  (l.take n)[i]? = l[i]?:= by
  grind
@[simp]
theorem pairwise_of_forall_eq
  {α : Type u} (c : α) (l : List α)
  (h : ∀ a ∈ l, a = c) :
  List.Pairwise (· = ·) l := by
  sorry
@[simp]
theorem take_append_gen (l₁ l₂ : List α) (n : Nat) :
    (l₁ ++ l₂).take n = (l₁.take n) ++ (l₂.take (n - l₁.length)) := by
  sorry
-- 正确的 simp 方向：把 take/drop 往里推，把 reverse 往外拉
@[simp] theorem reverse_take_eq (l : List α) (n : Nat) :
    (List.reverse l).take n = (l.drop (l.length - n)).reverse := by
  sorry

@[simp] theorem reverse_drop_eq (l : List α) (n : Nat) :
    (List.reverse l).drop n = (l.take (l.length - n)).reverse := by
  sorry
@[simp]
theorem Array.get_push_spec {α} (a : Array α) (v : α) (i : Nat) :
    (a.push v)[i]? = if i < a.size then a[i]? else if i = a.size then some v else none := by
  sorry
--这个要不要加则存疑
-- @[simp]
-- theorem getElem!_eq_getElem?_getD [Inhabited α] (a : Array α) (i : Nat) :
--     a[i]! = (a[i]?).getD default := by
--   sorry
@[simp]
theorem List.count_cons_of_ne {α} [DecidableEq α] (x a : α) (l : List α) (h : x ≠ a) :
    (a :: l).count x = l.count x := by
  grind

end TheoremsForCodeVerification
