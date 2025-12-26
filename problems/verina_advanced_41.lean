-- -----Description-----
-- This task requires writing a Lean 4 method that finds the maximum among three given integers. The method should return the largest value, ensuring that the result is greater than or equal to each of the input numbers and that it is one of the provided integers.
--
-- -----Input-----
-- The input consists of three integers:
-- a: The first integer.
-- b: The second integer.
-- c: The third integer.
--
-- -----Output-----
-- The output is an integer:
-- Returns the maximum of the three input numbers, assuring that the returned value is greater than or equal to a, b, and c, and that it matches one of these values.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  -- !benchmark @start postcond
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold maxOfThree_postcond maxOfThree
  simp
  grind
  -- !benchmark @end proof

--己。trivial
