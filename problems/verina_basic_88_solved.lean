-- -----Description-----
-- This task involves converting a list of integers into an array such that the array contains all the elements of the list in the exact same order. The objective is to ensure that the array has the same number of elements as the list and that each element in the array corresponds exactly to the element at the same position in the list.
--
-- -----Input-----
-- The input consists of:
-- • xs: A list of integer elements.
--
-- -----Output-----
-- The output is an array of elements of type integer that:
-- • Has a size equal to the length of the input list xs.
-- • Contains all the elements from xs in the same order, ensuring that for every valid index i, the array element at i is equal to the list element at i.
--
-- -----Note-----
-- There are no additional preconditions; the method should work correctly for any list of elements.
-- A corresponding specification is provided stating that the array’s size equals the list’s length and that each element is preserved.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ToArray_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  -- !benchmark @start code
  xs.toArray
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ToArray_postcond (xs : List Int) (result: Array Int) (h_precond : ToArray_precond (xs)) :=
  -- !benchmark @start postcond
  result.size = xs.length ∧ ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ToArray_spec_satisfied (xs: List Int) (h_precond : ToArray_precond (xs)) :
    ToArray_postcond (xs) (ToArray (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold ToArray_postcond ToArray
  grind
  -- !benchmark @end proof
--己。
