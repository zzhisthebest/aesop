-- -----Description-----  
-- This task is about processing an array of integers by producing a new array that excludes the first element. The objective is to define a clear behavior: if the array contains at least one element, return a modified array starting from the second element.
--
-- -----Input-----  
-- The input consists of:  
-- • a: An array of integers.
--
-- -----Output-----  
-- The output is an array of integers that:  
-- • Has a length equal to the original array's length minus one.  
-- • Contains the same elements as the input array except for the first element.  
-- • Satisfies the condition that for every index i in the output array, the element at position i is equal to the element at position i+1 in the input array.
--
-- -----Note-----  
-- It is assumed that the input array is non-empty.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def remove_front_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux
def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc
-- !benchmark @end code_aux


def remove_front (a : Array Int) (h_precond : remove_front_precond (a)) : Array Int :=
  -- !benchmark @start code
  if a.size > 0 then
    let c := copyFrom a 1 (Array.mkEmpty (a.size - 1))
    c
  else
    panic "Precondition violation: array is empty"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def remove_front_postcond (a : Array Int) (result: Array Int) (h_precond : remove_front_precond (a)) :=
  -- !benchmark @start postcond
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem remove_front_spec_satisfied (a: Array Int) (h_precond : remove_front_precond (a)) :
    remove_front_postcond (a) (remove_front (a) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

