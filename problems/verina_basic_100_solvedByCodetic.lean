-- -----Description-----
-- This task involves determining the triple of a given integer. The goal is to create a function that, for any integer provided as input, returns a value equal to three times that integer, including handling the case when the input is zero.
--
-- -----Input-----
-- The input consists of:
-- • x: An integer.
--
-- -----Output-----
-- The output is an integer that represents three times the input integer.
-- • If x = 0, the output will be 0.
-- • Otherwise, the output will be computed as x + 2 * x, which is equivalent to 3 * x.
--
-- -----Note-----
-- There are no additional preconditions. It is assumed that x is a valid integer.

-- !benchmark @start import type=solution
import Codetic
namespace tmp
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
  if x = 0 then 0 else
    let y := 2 * x
    x + y
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
  codetic
  unfold Triple_postcond Triple
  split_ifs with h₁
  . rw [h₁]
    simp
  . simp--用simp消去goal里的have
    rw (occs := [1]) [←Int.one_mul x]--新奇的用法
    rw [←Int.add_mul]
    simp +arith
  -- !benchmark @end proof
--己
