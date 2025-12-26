-- -----Description-----
-- Given a sorted list of distinct integers and a target value, return the index if the target is found. If it is not found, return the index where it would be inserted to maintain the sorted order.
--
-- This function must preserve the sorted property of the list. The list is assumed to be strictly increasing and contain no duplicates.
--
-- -----Input-----
-- xs : List Int — a sorted list of distinct integers in increasing order
-- target : Int — the integer to search for
--
-- -----Output-----
-- A natural number (Nat) representing the index at which the target is found, or the index at which it should be inserted to maintain sorted order.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· < ·) xs
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  -- !benchmark @start code
  match xs with
  | [] =>
      0
  | _ :: _ =>
      let rec helper : List Int → Nat → Nat :=
        fun ys idx =>
          match ys with
          | [] =>
              idx
          | y :: ys' =>
              let isCurrent := y
              let currentIndex := idx
              let targetValue := target
              let condition := targetValue ≤ isCurrent
              if condition then
                currentIndex
              else
                let incrementedIndex := currentIndex + 1
                let rest := ys'
                helper rest incrementedIndex
      let startingIndex := 0
      let result := helper xs startingIndex
      result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def searchInsert_postcond (xs : List Int) (target : Int) (result: Nat) (h_precond : searchInsert_precond (xs) (target)) : Prop :=
  -- !benchmark @start postcond
  let allBeforeLess := (List.range result).all (fun i => xs[i]! < target)
  let inBounds := result ≤ xs.length
  let insertedCorrectly :=
    result < xs.length → target ≤ xs[result]!
  inBounds ∧ allBeforeLess ∧ insertedCorrectly
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem searchInsert_spec_satisfied (xs: List Int) (target: Int) (h_precond : searchInsert_precond (xs) (target)) :
    searchInsert_postcond (xs) (target) (searchInsert (xs) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



