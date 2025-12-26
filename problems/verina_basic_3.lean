-- -----Description-----
-- This task requires writing a Lean 4 method that determines whether a given integer is divisible by 11. The method should return true if the number is divisible by 11 and false otherwise.
--
-- -----Input-----
-- The input consists of:
-- n: An integer to check for divisibility by 11.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the input number is divisible by 11.
-- Returns false if the input number is not divisible by 11.

-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isDivisibleBy11_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  -- !benchmark @start code
  n % 11 == 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isDivisibleBy11_postcond (n : Int) (result: Bool) (h_precond : isDivisibleBy11_precond (n)) :=
  -- !benchmark @start postcond
  (result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isDivisibleBy11_spec_satisfied (n: Int) (h_precond : isDivisibleBy11_precond (n)) :
    isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold isDivisibleBy11 isDivisibleBy11_postcond
  constructor
  · simp_all
    exact fun a => a
  · apply Not.imp_symm
    rw [not_forall_not]
    intro h
    rw [beq_iff_eq]
    exact Int.emod_eq_zero_of_dvd h--Int.emod_eq_zero_of_dvd很关键
  -- !benchmark @end proof
--己。
