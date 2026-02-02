/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 67be4c64-dbbd-4cf6-8835-b71c306ff728

The following was proved by Aristotle:

- theorem insertionSort_spec_satisfied (l: List Int) (h_precond : insertionSort_precond (l)) :
    insertionSort_postcond (l) (insertionSort (l) h_precond) h_precond
-/

import Codetic
import Mathlib

set_option maxHeartbeats 0

namespace verina_advanced_17

@[reducible]
def insertionSort_precond (l : List Int) : Prop :=
  True

def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)

def insertionSort (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  let result := sortList l
  result

@[reducible]
def insertionSort_postcond (l : List Int) (result: List Int) (h_precond : insertionSort_precond (l)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result

theorem insertionSort_spec_satisfied (l: List Int) (h_precond : insertionSort_precond (l)) :
    insertionSort_postcond (l) (insertionSort (l) h_precond) h_precond := by
      -- We'll use induction to prove that the list is sorted and a permutation.
      have h_ind : ∀ (l : List ℤ), List.Perm (verina_advanced_17.sortList l) l ∧ List.Sorted (· ≤ ·) (verina_advanced_17.sortList l) := by
        -- We'll use induction on the list to prove that `insertElement` maintains the sorted property and permutation.
        have h_insertElement : ∀ (x : ℤ) (l : List ℤ), List.Sorted (· ≤ ·) l → List.Sorted (· ≤ ·) (verina_advanced_17.insertElement x l) ∧ List.Perm (verina_advanced_17.insertElement x l) (x :: l) := by
          intros x l hl_sorted
          induction' l with y ys ih generalizing x;
          · simp [verina_advanced_17.insertElement];
          · by_cases hxy : x ≤ y <;> simp_all +decide [ verina_advanced_17.insertElement ];
            · exact fun a ha => le_trans hxy ( hl_sorted.1 a ha );
            · codetic?
        -- By induction on the list, we can show that `sortList` produces a sorted list and a permutation of the original list.
        intro l
        induction' l with x l ih;
        · trivial;
        ·
          -- Apply the induction hypothesis to the already sorted list `l`.
          have h_sorted : List.Sorted (· ≤ ·) (verina_advanced_17.insertElement x (verina_advanced_17.sortList l)) ∧ List.Perm (verina_advanced_17.insertElement x (verina_advanced_17.sortList l)) (x :: verina_advanced_17.sortList l) := by
            exact h_insertElement x _ ih.2;
          exact ⟨ h_sorted.2.trans ( List.Perm.cons _ ih.1 ), h_sorted.1 ⟩;
      -- Apply the induction hypothesis to split the conjunction into the two required parts.
      apply And.intro;
      · exact h_ind l |>.2;
      · convert h_ind l |>.1.symm using 1;
        exact?

end verina_advanced_17
