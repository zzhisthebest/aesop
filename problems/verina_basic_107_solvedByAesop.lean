-- -----Description-----
-- This task involves computing the average of two integers. The objective is to determine a value that closely approximates the true arithmetic mean when using integer division, ensuring that the result reflects the necessary rounding behavior.
--
-- -----Input-----
-- The input consists of:
-- • a: An integer.
-- • b: An integer.
--
-- -----Output-----
-- The output is an integer representing the computed average of a and b using integer division.
--
-- -----Note-----
-- The specification requires that the computed average satisfies the condition that 2 * avg is between (a + b - 1) and (a + b + 1), ensuring that the result meets the expected rounding boundaries.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
import Aesop
namespace tmp
-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  -- !benchmark @start code
  (a + b) / 2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  -- !benchmark @start postcond
  2 * result = a + b - ((a + b) % 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeAvg_spec_satisfied (a: Int) (b: Int) (h_precond : ComputeAvg_precond (a) (b)) :
    ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop
  -- !benchmark @end proof

--己。trivial
