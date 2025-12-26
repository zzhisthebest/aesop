-- -----Description-----
-- This task involves merging two sorted arrays of natural numbers (it is ill defined if inputs aren't sorted.)
-- -----Input-----
-- The input consists of two arrays:
-- a1: A sorted array of natural numbers
-- a2: A sorted array of natural numbers
-- -----Output-----
-- The output is an array:
-- Returns a new array with all elements from both input arrays (included once and only once)
-- The resulting array is sorted itself
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Array Nat :=
  -- !benchmark @start code
  Id.run <| do
    let mut i := 0
    let mut j := 0
    let mut result := #[]
    while i < a1.size ∧ j < a2.size do
      if a1[i]! ≤ a2[j]! then
        result := result.push a1[i]!
        i := i + 1
      else
        result := result.push a2[j]!
        j := j + 1
    while i < a1.size do
      result := result.push a1[i]!
      i := i + 1
    while j < a2.size do
      result := result.push a2[j]!
      j := j + 1
    return result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem mergeSorted_spec_satisfied (a1: Array Nat) (a2: Array Nat) :
    mergeSorted_postcond (a1) (a2) (mergeSorted (a1) (a2)) := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



