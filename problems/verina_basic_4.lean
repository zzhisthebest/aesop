-- -----Description-----
-- This task requires writing a Lean 4 method that finds the kth element in a given array using 1-based indexing. The method should return the element at the specified position, where the first element is at position 1.
--
-- -----Input-----
-- The input consists of:
-- arr: An array of integers.
-- k: An integer representing the position (1-based index) of the element to find.
--
-- -----Output-----
-- The output is an integer:
-- Returns the element at the kth position in the array.
--
-- -----Note-----
-- The input k is assumed to be valid (between 1 and array length inclusive).
-- The array is assumed to be non-empty.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≥ 1 ∧ k ≤ arr.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  -- !benchmark @start code
  arr[k - 1]!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  -- !benchmark @start postcond
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem kthElement_spec_satisfied (arr: Array Int) (k: Nat) (h_precond : kthElement_precond (arr) (k)) :
    kthElement_postcond (arr) (k) (kthElement (arr) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold kthElement kthElement_postcond
  unfold kthElement_precond at h_precond
  have ⟨hp1, hp2⟩ := h_precond
  simp_all
  have h': k - 1 < arr.size := by
    exact Nat.sub_one_lt_of_le hp1 hp2
  exists k - 1
  exists h'
  --exact Eq.symm (getElem!_pos arr (k - 1) ((Iff.of_eq (Eq.refl (k - 1 < arr.size))).mpr h'))
  rw [getElem!_pos]--getElem!_pos很关键
  -- refine Eq.symm (getElem!_pos arr (k - 1) ?_)
  -- assumption
  -- !benchmark @end proof
--己
