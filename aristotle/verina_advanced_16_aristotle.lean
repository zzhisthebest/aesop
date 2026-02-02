/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d411bf89-1e8c-4b1d-81a5-3611f0ef31ae

The following was proved by Aristotle:

- theorem insertionSort_spec_satisfied (xs: List Int) (h_precond : insertionSort_precond (xs)) :
    insertionSort_postcond (xs) (insertionSort (xs) h_precond) h_precond
-/

import Mathlib
import Codetic

set_option maxHeartbeats 0

namespace verina_advanced_16

@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  True

def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
    let rec insert (x : Int) (ys : List Int) : List Int :=
      match ys with
      | []      => [x]
      | y :: ys' =>
        if x <= y then
          x :: y :: ys'
        else
          y :: insert x ys'

    let rec sort (arr : List Int) : List Int :=
      match arr with
      | []      => []
      | x :: xs => insert x (sort xs)

    sort xs

@[reducible]
def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result

theorem insertionSort_spec_satisfied (xs: List Int) (h_precond : insertionSort_precond (xs)) :
    insertionSort_postcond (xs) (insertionSort (xs) h_precond) h_precond := by
      constructor;
      · revert xs h_precond;
        -- By definition of `insert`, if the input list is pairwise sorted, then the result of `insert x ys` is also pairwise sorted.
        have h_insert_sorted : ∀ x ys, List.Pairwise (· ≤ ·) ys → List.Pairwise (· ≤ ·) (verina_advanced_16.insertionSort.insert x ys) := by
          -- We'll use induction on the list `ys` to prove that inserting `x` into `ys` maintains the pairwise sorted property.
          intro x ys hys
          induction' ys with y ys ih generalizing x;
          · exact List.pairwise_singleton _ _;
          · by_cases hxy : x ≤ y <;> simp_all +decide [ verina_advanced_16.insertionSort.insert ];
            · exact fun a ha => le_trans hxy ( hys.1 a ha );
            · split_ifs <;> simp_all +decide [ not_le_of_gt ];
              -- By definition of insertion sort, if `x` is inserted into `ys`, then `x` is placed in the correct position to maintain the sorted order.
              have h_insert_pos : ∀ x ys, List.Pairwise (· ≤ ·) ys → ∀ a' ∈ insertionSort.insert x ys, x ≤ a' ∨ a' ∈ ys := by
                intros x ys hys a' ha'
                induction' ys with y ys ih generalizing x a';
                · -- In the base case, when `ys` is empty, the list after insertion is just `[x]`. Therefore, `a'` must be `x`, and the first part of the disjunction holds.
                  simp [verina_advanced_16.insertionSort.insert] at ha' ⊢
                  aesop;
                ·
                  by_cases hxy : x ≤ y <;> simp_all +decide [ verina_advanced_16.insertionSort.insert ];
                  · grind;
                  · grind;
              grind;
        intro xs h_precond;
        induction' xs with x xs ih;
        · exact List.Pairwise.nil;
        · exact h_insert_sorted x _ ( ih trivial );
      · -- By definition of insertion sort, the resulting list is a permutation of the original list.
        have h_perm : ∀ (xs : List ℤ), List.Perm xs (verina_advanced_16.insertionSort xs h_precond) := by
          intro xs;
          -- By definition of `insertionSort.insert`, inserting an element into a list preserves the permutation property.
          have h_insert_perm : ∀ (x : ℤ) (ys : List ℤ), List.Perm (x :: ys) (verina_advanced_16.insertionSort.insert x ys) := by
            -- By definition of `insert`, we know that inserting an element into a list results in a permutation of the original list. We can prove this by induction on the list `ys`.
            intros x ys
            induction' ys with y ys ih;
            · rfl;
            · by_cases h : x ≤ y <;> simp_all +decide [ List.perm_iff_count ];
              · -- In this case, inserting x into y :: ys results in x :: y :: ys, so the counts are the same.
                intros a
                simp [verina_advanced_16.insertionSort.insert, h];
              · -- By definition of `insert`, we know that inserting `x` into `y :: ys` results in `y :: insert x ys`.
                have h_insert : verina_advanced_16.insertionSort.insert x (y :: ys) = y :: verina_advanced_16.insertionSort.insert x ys := by
                  exact if_neg h.not_le;
                grind;
          -- By definition of `insertionSort.sort`, we can prove that it is a permutation of the original list by induction on the list.
          induction' xs with x xs ih;
          · rfl;
          · exact List.Perm.trans ( List.Perm.cons _ ih ) ( h_insert_perm _ _ );
        exact?

end verina_advanced_16
