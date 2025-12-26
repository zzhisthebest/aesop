-- -----Description-----
-- This task requires writing a Lean 4 method that locates the first occurrence of a specified integer within a sorted array of integers. The method returns the index corresponding to the first time the target value appears in the array; if the target is absent, it returns -1. It is also essential that the original array remains unchanged.
--
-- -----Input-----
-- The input consists of:
-- • arr: An array of integers sorted in non-decreasing order.
-- • target: An integer representing the value to search for.
--
-- -----Output-----
-- The output is an integer:
-- • If the target is found, the method returns the index of its first occurrence.
-- • If the target is not found, the method returns -1.
--
-- -----Note-----
-- • The input array must be sorted in non-decreasing order.
-- • The array is guaranteed to remain unmodified after the method executes.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findFirstOccurrence_spec_satisfied (arr: Array Int) (target: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    findFirstOccurrence_postcond (arr) (target) (findFirstOccurrence (arr) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findFirstOccurrence_precond at h_precond
  unfold findFirstOccurrence findFirstOccurrence_postcond
  constructor
  · intro h1
    constructor
    · sorry
    · let i := 0
      induction i using findFirstOccurrence.loop.induct arr target with
      | case1 i h_bound =>
        sorry
      | case2 i h_bound  =>
        sorry
      | case3 i h_bound  =>
        sorry
      | case4 i h_bound  =>
        sorry

      sorry
  · intro h1
    sorry

  -- !benchmark @end proof
