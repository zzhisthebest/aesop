-- -----Description-----
-- Given an integer x, determine a pair (a, b) where the first element is twice the value of x and the second element is four times the value of x.
--
-- -----Input-----
-- The input consists of:
-- • x: An integer.
--
-- -----Output-----
-- The output is a tuple (a, b) where:
-- • a = 2 * x
-- • b = 4 * x
--
-- -----Note-----
-- There are no additional preconditions; the method is defined for all integers.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
namespace tmp
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  -- !benchmark @start code
  let a := 2 * x
  let b := 2 * a
  (a, b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  -- !benchmark @start postcond
  result.fst = 2 * x ∧ result.snd = 2 * result.fst
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem DoubleQuadruple_spec_satisfied (x: Int) (h_precond : DoubleQuadruple_precond (x)) :
    DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  -- !benchmark @end proof
--己
