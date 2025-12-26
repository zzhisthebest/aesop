-- -----Description-----
-- This problem involves computing the triple of a given integer. The goal is to produce an output that is exactly three times the input value.
--
-- -----Input-----
-- The input consists of:
-- • x: An integer representing the value to be tripled.
--
-- -----Output-----
-- The output is an integer that is three times the input value (i.e., 3 * x).
--
-- -----Note-----
-- The implementation uses a local variable to first compute double the input and then adds the original input to get the final result. The accompanying theorem asserts that the function satisfies the specification of computing 3 * x.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  let y := x * 2
  y + x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  -- !benchmark @start postcond
  result / 3 = x ∧ result / 3 * 3 = result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold Triple_postcond Triple
  simp
  rw (occs := [2]) [←Int.mul_one x]
  rw [←Int.mul_add]
  simp +arith
  -- !benchmark @end proof
--己。trivial
