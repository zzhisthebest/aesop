-- -----Description-----
-- This task focuses on determining if a given integer is even. The problem requires checking whether the integer can be represented as twice another integer, meaning it is divisible by 2 without any remainder.
--
-- -----Input-----
-- The input consists of a single integer:
-- • x: An integer to be evaluated.
--
-- -----Output-----
-- The output is a boolean value:
-- • true if x is even (x mod 2 equals 0).
-- • false if x is odd.
--
-- -----Note-----
-- No additional preconditions are required. The method should work correctly for any integer value.

-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  -- !benchmark @start code
  if x % 2 = 0 then true else false
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ k : Int, x = 2 * k
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeIsEven_spec_satisfied (x: Int) (h_precond : ComputeIsEven_precond (x)) :
    ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold ComputeIsEven ComputeIsEven_postcond
  simp
  rfl
  -- !benchmark @end proof
--己
