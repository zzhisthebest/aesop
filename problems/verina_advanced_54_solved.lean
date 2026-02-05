-- -----Description-----
-- This task requires writing a Lean 4 function that finds the one missing number in a list of distinct natural numbers from 0 to n. The list contains exactly n numbers and all numbers are in the range [0, n], but one number in that range is missing.
--
-- Your function must return the missing number. You may assume the input list contains no duplicates and only one number is missing.
--
-- -----Input-----
-- - nums: A list of natural numbers of length n, each in the range [0, n] with exactly one number missing.
--
-- -----Output-----
-- - A natural number: the missing number in the range [0, n] not present in the list.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  -- !benchmark @start code
  let n := nums.length
  let expectedSum := (n * (n + 1)) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def missingNumber_postcond (nums : List Nat) (result: Nat) (h_precond : missingNumber_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem missingNumber_spec_satisfied (nums: List Nat) (h_precond : missingNumber_precond (nums)) :
    missingNumber_postcond (nums) (missingNumber (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



