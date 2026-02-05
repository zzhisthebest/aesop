-- -----Description-----
-- This task requires writing a Lean 4 method that converts all uppercase characters in a given string to their lowercase equivalents while keeping the other characters unchanged. The output string must have the same length as the input string.
--
-- -----Input-----
-- The input consists of:
-- s: A string that may contain both uppercase and lowercase characters.
--
-- -----Output-----
-- The output is a string:
-- Returns a new string where every uppercase letter has been converted to lowercase, and every non-uppercase character remains exactly as in the input.
--
-- -----Note-----
-- There are no preconditions; the method is expected to work for any non-null string.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toLowercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  -- !benchmark @start code
  let cs := s.toList
  let cs' := cs.map (fun c => if isUpperCase c then shift32 c else c)
  String.mk cs'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def toLowercase_postcond (s : String) (result: String) (h_precond : toLowercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem toLowercase_spec_satisfied (s: String) (h_precond : toLowercase_precond (s)) :
    toLowercase_postcond (s) (toLowercase (s) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold toLowercase toLowercase_postcond
  simp_all
  constructor
  · unfold String.length
    simp
  ·
    intro i hi
    have hi' : i < s.data.length := by--为了让simp_all起作用
      unfold String.length at hi
      simp at hi
      exact hi
    constructor <;> simp_all
  -- !benchmark @end proof
--己。
