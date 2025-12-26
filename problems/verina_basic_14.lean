-- -----Description-----
-- This task requires writing a Lean 4 method that determines whether a given string contains the character 'z' or 'Z'. The method should return true if the string includes either the lowercase or uppercase letter 'z', and false otherwise.
--
-- -----Input-----
-- The input consists of:
-- s: A string.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the input string contains the character 'z' or 'Z'.
-- Returns false if the input string does not contain the character 'z' or 'Z'.
--
-- -----Note-----
-- There are no preconditions; the method will always work as strings and sequences are considered non-null.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  -- !benchmark @start code
  s.toList.any fun c => c = 'z' || c = 'Z'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem containsZ_spec_satisfied (s: String) (h_precond : containsZ_precond (s)) :
    containsZ_postcond (s) (containsZ (s) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold containsZ containsZ_postcond
  simp_all
  -- !benchmark @end proof
--己
