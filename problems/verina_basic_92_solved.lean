-- -----Description-----
-- This problem involves swapping the values of two integers. Given two integers as inputs, the objective is to return the two numbers in reversed order.
--
-- -----Input-----
-- The input consists of two integers:
-- • X: The first integer.
-- • Y: The second integer.
--
-- -----Output-----
-- The output is a tuple of two integers (Int × Int) where:
-- • The first element is equal to Y.
-- • The second element is equal to X.
--
-- -----Note-----
-- There are no restrictions on the input values. The function must correctly swap the inputs regardless of whether they are positive, negative, or zero.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  -- !benchmark @start code
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := y2 + x2
  (x3, y2)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapArithmetic_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold SwapArithmetic_postcond SwapArithmetic
  simp
  grind
  -- rw [Int.sub_sub_self]
  -- simp_all
  -- exact fun a a_1 => a (id (Eq.symm a_1))
  -- !benchmark @end proof
--己。
