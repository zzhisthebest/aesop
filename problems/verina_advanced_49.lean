-- -----Description-----
-- Implement a Lean 4 function that merges two ascendingly sorted lists of integers into one single sorted list (ascending). The resulting list must contain all elements from both input lists, preserving their ascending order.
--
-- -----Input-----
-- The input consists of two lists of integers:
-- arr1: A sorted list of integers (ascending)
-- arr2: Another sorted list of integers (ascending)
--
-- -----Output-----
-- The output is a list of integers:
-- Returns a new list containing all elements from arr1 and arr2, sorted in ascending order.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def mergeSortedLists (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : List Int :=
  -- !benchmark @start code
  let rec merge (xs : List Int) (ys : List Int) : List Int :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xt, y :: yt =>
      if x <= y then
        x :: merge xt (y :: yt)
      else
        y :: merge (x :: xt) yt

  merge arr1 arr2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def mergeSortedLists_postcond (arr1 : List Int) (arr2 : List Int) (result: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem mergeSortedLists_spec_satisfied (arr1: List Int) (arr2: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) :
    mergeSortedLists_postcond (arr1) (arr2) (mergeSortedLists (arr1) (arr2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



