-- -----Description-----
-- This task requires writing a Lean 4 method that calculates the surface area of a cube based on the length of one of its edges. The method should compute the surface area using the standard formula for a cube.
--
-- -----Input-----
-- The input consists of:
-- size: An natural number representing the length of an edge of the cube.
--
-- -----Output-----
-- The output is an natural number:
-- Returns the surface area of the cube.
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def cubeSurfaceArea_precond (size : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  -- !benchmark @start code
  6 * size * size
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def cubeSurfaceArea_postcond (size : Nat) (result: Nat) (h_precond : cubeSurfaceArea_precond (size)) :=
  -- !benchmark @start postcond
  result - 6 * size * size = 0 ∧ 6 * size * size - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem cubeSurfaceArea_spec_satisfied (size: Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold cubeSurfaceArea cubeSurfaceArea_postcond
  simp
  -- !benchmark @end proof
--己
