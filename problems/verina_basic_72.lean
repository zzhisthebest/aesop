-- -----Description-----  
-- The problem asks you to construct a new list by adding an extra number to the end of an existing list of numbers. The focus is on understanding what the final list should look like when a given number is included as the last element.
--
-- -----Input-----  
-- The input consists of:  
-- • a: An array of integers.  
-- • b: An integer to be appended to the array.
--
-- -----Output-----  
-- The output is an array of integers which represents the original array with the element b added at the end. That is, the output array’s list representation equals a.toList concatenated with [b].
--
-- -----Note-----  
-- There are no special preconditions; the method is expected to work correctly for any array of integers and any integer b.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def append_precond (a : Array Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc
-- !benchmark @end code_aux


def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let c_initial := copy a 0 (Array.empty)
  let c_full := c_initial.push b
  c_full
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def append_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : append_precond (a) (b)) :=
  -- !benchmark @start postcond
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem append_spec_satisfied (a: Array Int) (b: Int) (h_precond : append_precond (a) (b)) :
    append_postcond (a) (b) (append (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

