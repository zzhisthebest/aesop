-- -----Description-----
-- This task requires writing a Lean 4 method that rearranges an array of integers by moving all zero values to the end of the array. The method should ensure that the relative order of the non-zero elements remains the same, the overall size of the array is unchanged, and the number of zeroes in the array stays constant.
--
-- -----Input-----
-- The input consists of:
-- arr: An array of integers.
--
-- -----Output-----
-- The output is an array of integers:
-- Returns an array where:
-- - The length is the same as that of the input array.
-- - All zero values are positioned at the end.
-- - The relative order of non-zero elements is preserved.
-- - The count of zero values remains the same as in the input array.
--
-- -----Note-----
-- There are no preconditions; the method will always work for any array of integers.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  -- !benchmark @start code
  let nonZeros := arr.toList.filter (· ≠ 0)
  let zeros := arr.toList.filter (· = 0)
  Array.mk (nonZeros ++ zeros)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :=
  -- !benchmark @start postcond
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem MoveZeroesToEnd_spec_satisfied (arr: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    MoveZeroesToEnd_postcond (arr) (MoveZeroesToEnd (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop
  sorry
  -- !benchmark @end proof
