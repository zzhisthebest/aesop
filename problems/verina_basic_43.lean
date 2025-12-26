-- -----Description----- 
-- This task requires writing a Lean 4 method that computes the sum of the fourth power of the first n odd natural numbers. In other words, given a non-negative integer n, the method should calculate the sum: 1⁴ + 3⁴ + 5⁴ + ... for the first n odd numbers.
--
-- -----Input-----
-- The input consists of:
-- n: A non-negative natural number representing the number of odd natural numbers to consider.
--
-- -----Output----- 
-- The output is a natural number:
-- Returns the sum of the fourth power of the first n odd natural numbers.
--
-- -----Note----- 
-- The input n is assumed to be a non-negative integer.
-- The correctness of the result is established by a theorem that relates the computed sum to a specific formula.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  -- !benchmark @start code
  match n with
  | 0 => 0
  | n + 1 =>
    let prev := sumOfFourthPowerOfOddNumbers n h_precond
    let nextOdd := 2 * n + 1
    prev + nextOdd^4
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  -- !benchmark @start postcond
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumOfFourthPowerOfOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    sumOfFourthPowerOfOddNumbers_postcond (n) (sumOfFourthPowerOfOddNumbers (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

