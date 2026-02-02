-- -----Description-----
-- This task requires writing a Lean 4 method that finds the last occurrence of a specified element in a sorted array of integers. The method should return the index corresponding to the last occurrence of the element if it is present; if the element is absent, it should return -1. Additionally, the array must remain unchanged after the method is executed.
--
-- -----Input-----
-- The input consists of:
-- arr: A sorted array of integers in non-decreasing order.
-- elem: An integer whose last occurrence position is to be determined.
--
-- -----Output-----
-- The output is an integer:
-- Returns the index of the last occurrence of the specified integer in the array if it exists.
-- Returns -1 if the integer is not found in the array.
--
-- -----Note-----
-- The input array is assumed to be sorted in non-decreasing order and remains unchanged by the method.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
namespace tmp
@[reducible, simp]
def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (i + 1) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lastPosition_spec_satisfied (arr: Array Int) (elem: Int) (h_precond : lastPosition_precond (arr) (elem)) :
    lastPosition_postcond (arr) (elem) (lastPosition (arr) (elem) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  sorry
  -- !benchmark @end proof
