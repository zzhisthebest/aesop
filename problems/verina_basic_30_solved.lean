-- -----Description-----
-- This task requires writing a Lean 4 method that computes the element-wise modulo between two arrays of integers. The method should produce a new array where each element is the remainder after dividing the corresponding element from the first array by the element from the second array.
--
-- -----Input-----
-- The input consists of:
-- a: An array of integers.
-- b: An array of integers.
--
-- -----Output-----
-- The output is an array of integers:
-- Returns a new array in which each element is the result of taking the modulo of the corresponding elements from the two input arrays.
--
-- -----Note-----
-- Preconditions:
-- - Both arrays must be non-null.
-- - Both arrays must have the same length.
-- - All elements in the second array should be non-zero.
--
-- Postconditions:
-- - The length of the resulting array is the same as the length of the input arrays.
-- - Each element in the resulting array is the modulo of the corresponding elements in the input arrays.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def elementWiseModulo_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def elementWiseModulo (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  a.mapIdx (fun i x => x % b[i]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def elementWiseModulo_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.size = a.size ∧
  (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem elementWiseModulo_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    elementWiseModulo_postcond (a) (b) (elementWiseModulo (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold elementWiseModulo elementWiseModulo_postcond
  unfold elementWiseModulo_precond at h_precond
  simp_all
  -- intro i hi
  -- have h_maplen : (Array.mapIdx (fun i x => x % b[i]!) a).size = a.size := by
  --   apply Array.size_mapIdx
  -- have h1 : (Array.mapIdx (fun i x => x % b[i]!) a)[i] = (fun i x => x % b[i]!) i a[i] := by
  --   apply Array.getElem_mapIdx
  -- have h_eq : (Array.mapIdx (fun i x => x % b[i]!) a)[i] = (Array.mapIdx (fun i x => x % b[i]!) a)[i]! := by
  --   have hi' : i < (Array.mapIdx (fun i x => x % b[i]!) a).size := by
  --     simp only [h_precond, hi, h_maplen]
  --   rw [Array.getElem!_eq_getD]
  --   unfold Array.getD
  --   simp [hi', hi, h_precond]
  -- rw [← h_eq]
  -- simp only [h1]
  -- have h_eq' : a[i] = a[i]! := by
  --   have hi_a : i < a.size := by
  --     simp only [h_precond, hi]
  --   simp_all [Array.getElem!_eq_getD]
  -- simp only [h_eq']
  -- !benchmark @end proof
--己。trivial
