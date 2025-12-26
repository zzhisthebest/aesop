-- -----Description-----
-- This task requires writing a Lean 4 method that extracts the last digit of a given non-negative integer. The method should return the last digit, which is obtained by computing the remainder when the number is divided by 10. The result must always be between 0 and 9.
--
-- -----Input-----
-- The input consists of a single value:
-- n: A non-negative integer.
--
-- -----Output-----
-- The output is an integer:
-- Returns the last digit of the input number, ensuring that the digit lies within the range 0 to 9.
--
-- -----Note-----
-- It is assumed that the input number n is non-negative.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  -- !benchmark @start code
  n % 10
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  -- !benchmark @start postcond
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lastDigit_spec_satisfied (n: Nat) (h_precond : lastDigit_precond (n)) :
    lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold lastDigit lastDigit_postcond
  constructor
  · constructor
    · simp
    ·
      exact Nat.mod_lt n (by trivial)
  · simp
  -- !benchmark @end proof
--己
