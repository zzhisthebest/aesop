-- -----Description-----
-- This task requires writing a Lean 4 method that determines whether a given integer is even. In other words, the method should return true if the number is even and false if the number is odd.
--
-- -----Input-----
-- The input consists of:
-- n: An integer.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the input number is even.
-- Returns false if the input number is odd.
--
-- -----Note-----
-- There are no preconditions; the method will always work for any integer input.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  -- !benchmark @start code
  n % 2 == 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  -- !benchmark @start postcond
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold isEven isEven_postcond
  simp
  -- !benchmark @end proof
--己
