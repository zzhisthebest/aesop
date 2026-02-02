-- -----Description-----
-- This task requires writing a Lean 4 method that determines whether two given integers have opposite signs. In other words, the method should return true if one integer is positive and the other is negative. Note that zero is considered neither positive nor negative; therefore, if either integer is zero, the method should return false.
--
-- -----Input-----
-- The input consists of two integers:
-- a: An integer.
-- b: An integer.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if one of the integers is positive and the other is negative (i.e., they have opposite signs).
-- Returns false if both integers are either non-negative or non-positive, or if one (or both) is zero.

-- !benchmark @start import type=solution
import Codetic
namespace tmp
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  a * b < 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  -- !benchmark @start postcond
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧--'→'就是数学上的'=>'
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasOppositeSign_spec_satisfied (a: Int) (b: Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  linarith
  unfold hasOppositeSign hasOppositeSign_postcond
  constructor

  · --codetic
    intro h
    cases h with
    | inl h1 =>
      simp
      codetic
    | inr h2 =>
      simp
      have ⟨ha, hb⟩ := h2
      rw [Int.mul_comm]
      exact Int.mul_neg_of_neg_of_pos hb ha
  -- . rw [Bool.decide_iff, mul_neg_iff]
  --   rw [Or.comm]
  --   simp
  · codetic
    rw [Bool.decide_iff, mul_neg_iff]
    simp_all
  -- !benchmark @end proof
end tmp
--己
