-- -----Description-----
-- This task requires swapping two integer values. Given two integers as input, the objective is to produce an output where their order is reversed: the first element of the output corresponds to the second input and the second element corresponds to the first input.
--
-- -----Input-----
-- The input consists of two integers:
-- • X: An integer value.
-- • Y: Another integer value.
--
-- -----Output-----
-- The output is a tuple (Int × Int) where:
-- • The first element is equal to Y.
-- • The second element is equal to X.
--
-- -----Note-----
-- There are no additional preconditions for this task. The function simply returns a swapped tuple of its two input integers.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
import Codetic
namespace tmp
-- !benchmark @end precond_aux
@[reducible, simp]
def SwapSimultaneous_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  (Y, X)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapSimultaneous_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapSimultaneous_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  -- exact fun a a_1 => a (id (Eq.symm a_1))
  -- !benchmark @end proof
--己。
