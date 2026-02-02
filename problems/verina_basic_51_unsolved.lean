-- -----Description-----
-- This task requires creating a function that determines the correct insertion index for a given integer in a sorted array. The goal is to identify an index where every number before it is less than the specified value, and every number from that index onward is greater than or equal to the value. If the given integer is larger than all elements in the array, the function should return the array’s size.
--
-- -----Input-----
-- The input consists of:
-- • a: An array of integers that is assumed to be sorted in non-decreasing order.
-- • key: An integer to search for in the array.
--
-- -----Output-----
-- The output is a natural number (Nat) representing the index determined by the binary search. The index satisfies the following postconditions:
-- • It is between 0 and the size of the array.
-- • Every element before the returned index is less than the key.
-- • If the returned index equals the size of the array, then all elements are less than the key.
-- • Every element from the index onwards is greater than or equal to the key.
--
-- -----Note-----
-- It is assumed that the input array is sorted in non-decreasing order. The function returns the first index where the key could be inserted while maintaining the sorted order.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
namespace tmp
@[reducible, simp]
def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux
def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo
-- !benchmark @end code_aux


def BinarySearch (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) : Nat :=
  -- !benchmark @start code
  binarySearchLoop a key 0 a.size
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def BinarySearch_postcond (a : Array Int) (key : Int) (result: Nat) (h_precond : BinarySearch_precond (a) (key)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem BinarySearch_spec_satisfied (a: Array Int) (key: Int) (h_precond : BinarySearch_precond (a) (key)) :
    BinarySearch_postcond (a) (key) (BinarySearch (a) (key) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  sorry
  -- !benchmark @end proof
