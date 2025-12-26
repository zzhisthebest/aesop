-- -----Description-----
-- This task requires writing a Lean 4 method that checks whether an array of integers is sorted in non-decreasing order. The method should return true if every element is less than or equal to the element that follows it, and false otherwise.
--
-- -----Input-----
-- The input consists of:
-- a: An array of integers. The array can be empty or have any length.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the array is sorted in non-decreasing order.
-- Returns false if the array is not sorted in non-decreasing order.
--
-- -----Note-----
-- A true result guarantees that for every valid pair of indices i and j (with i < j), the element at position i is less than or equal to the element at position j. A false result indicates that there exists at least one adjacent pair of elements where the first element is greater than the second.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def isSorted_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux
#check Array.all

def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  -- !benchmark @start code
  if a.size ≤ 1 then
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[i + 1])
      else
        true) |>.all id
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isSorted_postcond (a : Array Int) (result: Bool) (h_precond : isSorted_precond (a)) :=
  -- !benchmark @start postcond
  (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isSorted_spec_satisfied (a: Array Int) (h_precond : isSorted_precond (a)) :
    isSorted_postcond (a) (isSorted (a) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop

  -- !benchmark @end proof
--己
