-- -----Description-----
-- This task requires determining the smaller of two integers. Given two input numbers, the goal is to compare them and return the one that is less than or equal to the other.
--
-- -----Input-----
-- The input consists of two integers:
-- • x: The first integer.
-- • y: The second integer.
--
-- -----Output-----
-- The output is an integer representing the minimum of the two input integers:
-- • Returns x if x is less than or equal to y.
-- • Returns y if x is greater than y.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def myMin_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  -- !benchmark @start code
  if x < y then x else y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def myMin_postcond (x : Int) (y : Int) (result: Int) (h_precond : myMin_precond (x) (y)) :=
  -- !benchmark @start postcond
  (x ≤ y → result = x) ∧ (x > y → result = y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem myMin_spec_satisfied (x: Int) (y: Int) (h_precond : myMin_precond (x) (y)) :
    myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold myMin_postcond myMin
  simp
  grind
  -- have h_left : (x ≤ y → y ≤ x → y = x) := by
  --   intro h₁ h₂
  --   exact Int.le_antisymm h₂ h₁
  -- have h_right : (y < x → x < y → x = y) := by
  --   intro h₁ h₂
  --   have h_contr : False := Int.lt_irrefl x (Int.lt_trans h₂ h₁)
  --   contradiction
  -- exact ⟨h_left, h_right⟩
  -- !benchmark @end proof
--己
