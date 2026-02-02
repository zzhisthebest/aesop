-- -----Description-----
-- This problem involves swapping two elements in an array of integers at specified positions. Given an array and two indices, the task is to exchange these elements so that the element from the first index moves to the second index and vice versa, while all other elements remain unchanged.
--
-- -----Input-----
-- The input consists of:
-- • arr: An array of integers.
-- • i: An integer representing the first index (0-indexed) whose element is to be swapped.
-- • j: An integer representing the second index (0-indexed) whose element is to be swapped.
--
-- -----Output-----
-- The output is an array of integers which:
-- • Has the same size as the input array.
-- • Contains the element originally at index i in position j and the element originally at index j in position i.
-- • Leaves all other elements unchanged.
--
-- -----Note-----
-- It is assumed that both indices i and j are non-negative and within the bounds of the array (i.e., Int.toNat i and Int.toNat j are less than arr.size).

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
namespace tmp
@[reducible, simp]
def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  -- !benchmark @start precond
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  -- !benchmark @start code
  let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) (h_precond : swap_precond (arr) (i) (j)) :=
  -- !benchmark @start postcond
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem swap_spec_satisfied (arr: Array Int) (i: Int) (j: Int) (h_precond : swap_precond (arr) (i) (j)) :
    swap_postcond (arr) (i) (j) (swap (arr) (i) (j) h_precond) h_precond := by
  -- !benchmark @start proof
  --unfold swap_postcond swap
  codetic?
  -- !benchmark @end proof
end tmp
