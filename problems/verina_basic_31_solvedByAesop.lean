-- -----Description-----
-- This task requires writing a Lean 4 method that converts a given string to uppercase. The method should replace every lowercase letter in the input string with its corresponding uppercase character while leaving all other characters unchanged. The output string must have the same length as the input string.
--
-- -----Input-----
-- The input consists of:
-- s: A string.
--
-- -----Output-----
-- The output is a string:
-- Returns a new string in which every lowercase letter from the input string is converted to uppercase, and all other characters are exactly the same as in the input string, ensuring the output string has the same length as the input.
--
-- -----Note-----
-- There are no preconditions since the method assumes that the input string is always valid (i.e., non-null).

-- !benchmark @start import type=solution

-- !benchmark @end import
import Aesop
namespace tmp
-- !benchmark @start solution_aux
def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toUppercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  -- !benchmark @start code
  let cs := s.toList
  let cs' := cs.map (fun c => if isLowerCase c then shiftMinus32 c else c)
  String.mk cs'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem toUppercase_spec_satisfied (s: String) (h_precond : toUppercase_precond (s)) :
    toUppercase_postcond (s) (toUppercase (s) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop
    -- have hi' : i < s.data.length := by
    --   unfold String.length at hi
    --   simp at hi
    --   exact hi
    -- constructor <;> simp_all
  -- !benchmark @end proof
--己。trivial
