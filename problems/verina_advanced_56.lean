-- -----Description-----
-- This task requires writing a Lean 4 method that moves all zeroes in a given integer list to the end, while preserving the relative order of the non-zero elements.
--
-- The method `moveZeroes` processes the input list by separating the non-zero and zero elements. It then returns a new list formed by appending all non-zero elements followed by all the zero elements.
--
-- -----Input-----
-- The input is a single list of integers:
-- xs: A list of integers (type: List Int), possibly containing zero and non-zero values.
--
-- -----Output-----
-- The output is a list of integers:
-- Returns a list (type: List Int) with the same elements as the input, where all zeroes appear at the end, and the non-zero elements maintain their original relative order.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def moveZeroes_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- Count how many times a specific value appears in the list

-- !benchmark @end code_aux


def moveZeroes (xs : List Int) (h_precond : moveZeroes_precond (xs)) : List Int :=
  -- !benchmark @start code
  let nonzeros := xs.filter (fun x => x ≠ 0)
  let zeros := xs.filter (fun x => x = 0)
  nonzeros ++ zeros
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

-- Check whether one list is a subsequence of another (preserving relative order)
def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt
-- !benchmark @end postcond_aux


@[reducible]
def moveZeroes_postcond (xs : List Int) (result: List Int) (h_precond : moveZeroes_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  -- 1. All non-zero elements must maintain their relative order
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧

  -- 2. All zeroes must be located at the end of the output list
  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧

  -- 3. The output must contain the same number of elements,
  --    and the number of zeroes must remain unchanged
  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem moveZeroes_spec_satisfied (xs: List Int) (h_precond : moveZeroes_precond (xs)) :
    moveZeroes_postcond (xs) (moveZeroes (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



