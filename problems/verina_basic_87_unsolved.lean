-- -----Description-----
-- This problem requires sorting an array of integers into non-decreasing order, ensuring that the output contains exactly the same elements as the input (i.e., it is a permutation of the original array).
--
-- -----Input-----
-- The input consists of:
-- • a: An array of integers (Array Int).
--
-- -----Output-----
-- The output is an array of integers that is:
-- • Sorted in non-decreasing order.
-- • A permutation of the input, meaning it contains exactly the same elements (with the same multiplicities) as the original array.
--
-- -----Note-----
-- It is assumed that the input array is valid and that the swap operations, along with the helper functions, correctly implement the selection sort algorithm.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
import Codetic
namespace tmp
-- !benchmark @end precond_aux
@[reducible, simp]
def SelectionSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a
-- !benchmark @end code_aux


def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  -- !benchmark @start code
  let indices := List.range a.size
  indices.foldl (fun arr i =>
    let minIdx := findMinIndexInRange arr i a.size
    swap arr i minIdx
  ) a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SelectionSort_spec_satisfied (a: Array Int) (h_precond : SelectionSort_precond (a)) :
    SelectionSort_postcond (a) (SelectionSort (a) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  -- !benchmark @end proof
