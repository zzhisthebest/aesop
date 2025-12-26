-- -----Description-----  
-- This task involves identifying the maximum value in a non-empty array of integers. The objective is to determine which element in the array is greater than or equal to every other element, ensuring that the selected value is one of the elements in the array.
--
-- -----Input-----  
-- The input consists of:  
-- • a: An array of integers. It is assumed that the array is non-empty (i.e., its size is at least 1).
--
-- -----Output-----  
-- The output is an integer that represents the maximum element in the array. This value is guaranteed to satisfy the following:  
-- • It is greater than or equal to every element in the array.  
-- • It is exactly equal to one of the elements in the array.
--
-- -----Note-----  
-- It is assumed that the provided array is non-empty. In cases where the array is empty, the function's behavior is not defined.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxArray_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux
def maxArray_aux (a : Array Int) (index : Nat) (current : Int) : Int :=
  if index < a.size then
    let new_current := if current > a[index]! then current else a[index]!
    maxArray_aux a (index + 1) new_current
  else
    current
-- !benchmark @end code_aux


def maxArray (a : Array Int) (h_precond : maxArray_precond (a)) : Int :=
  -- !benchmark @start code
  maxArray_aux a 1 a[0]!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxArray_postcond (a : Array Int) (result: Int) (h_precond : maxArray_precond (a)) :=
  -- !benchmark @start postcond
  (∀ (k : Nat), k < a.size → result >= a[k]!) ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxArray_spec_satisfied (a: Array Int) (h_precond : maxArray_precond (a)) :
    maxArray_postcond (a) (maxArray (a) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

