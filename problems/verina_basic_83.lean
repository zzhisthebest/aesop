-- -----Description-----  
-- This task involves concatenating two arrays of integers by appending the second array to the end of the first array. The goal is to produce a new array that sequentially contains all elements from the first array followed by all elements from the second array.
--
-- -----Input-----  
-- The input consists of two parameters:  
-- • a: An Array of integers representing the first part of the concatenated array.  
-- • b: An Array of integers representing the second part of the concatenated array.
--
-- -----Output-----  
-- The output is an Array of integers that satisfies the following:  
-- • The length of the output array is equal to the sum of the lengths of arrays a and b.  
-- • The first part of the output array (indices 0 to a.size - 1) is identical to array a.  
-- • The remaining part of the output array (indices a.size to a.size + b.size - 1) is identical to array b.
--
-- -----Note-----  
-- No additional preconditions are required since the function uses the sizes of the input arrays to build the resulting array.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let n := a.size + b.size
  let rec loop (i : Nat) (c : Array Int) : Array Int :=
    if i < n then
      let value := if i < a.size then a[i]! else b[i - a.size]!
      loop (i + 1) (c.set! i value)
    else
      c
  loop 0 (Array.mkArray n 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : concat_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem concat_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : concat_precond (a) (b)) :
    concat_postcond (a) (b) (concat (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

