-- -----Description-----
-- This task requires writing a Lean 4 method that finds the minimum among three given integers. The method should return the smallest value, ensuring that the result is less than or equal to each of the input numbers and that it is one of the provided integers.
--
-- -----Input-----
-- The input consists of three integers:
-- a: The first integer.
-- b: The second integer.
-- c: The third integer.
--
-- -----Output-----
-- The output is an integer:
-- Returns the minimum of the three input numbers, assuring that the returned value is less than or equal to a, b, and c, and that it matches one of these values.

-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold minOfThree minOfThree_postcond

  split

  -- Case 1: a is the minimum
  -- · by_cases h1: a <= b && a <= c--by_cases是为了给split产生的unnamed hypothesis命名
  --   · simp_all
  --   · contradiction
  simp_all
  split

  -- Case 2: b is the minimum
  -- · by_cases h2: b <= a && b <= c
  --   · simp_all
  --   · contradiction

  -- Case 3: c is the minimum
  simp_all
  rename_i h1 h2
  simp_all
  by_cases h3: a<=b
  · simp_all
    constructor
    · exact le_of_lt h1
    · apply le_trans _ h3
      apply le_of_lt h1
  · simp_all
    apply le_of_lt at h3
    simp_all
    constructor
    · apply le_trans _ h3
      apply le_of_lt h2
    · apply le_of_lt h2


  -- · by_cases h3: c < a && c < b
  --   · constructor
  --     · simp_all
  --       constructor
  --       · exact le_of_lt h3.1
  --       · exact le_of_lt h3.2
  --     · simp
  --   · constructor
  --     · simp_all
  --       by_cases h': a <= b
  --       · simp_all
  --         have h'': a <= c := by
  --           exact le_trans h' h3
  --         rw [← not_lt] at h''
  --         contradiction
  --       · simp_all
  --         have _: b <= a := by exact le_of_lt h'
  --         simp_all
  --         have h'': c < b := by assumption
  --         have h''': c < a := by exact lt_trans h'' h'
  --         apply h3 at h'''
  --         rw [← not_lt] at h'''
  --         contradiction
  --     · simp
  -- !benchmark @end proof
--己
