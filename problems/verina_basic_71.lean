-- -----Description-----  
-- This problem involves determining the longest common prefix shared by two lists of characters. Given two sequences, the goal is to identify and return the maximal contiguous sequence of characters from the beginning of both lists that are identical. 
--
-- -----Input-----  
-- The input consists of:  
-- • str1: A list of characters.  
-- • str2: A list of characters.
--
-- -----Output-----  
-- The output is a list of characters representing the longest common prefix of the two input lists. The output list satisfies the following conditions:  
-- • Its length is less than or equal to the length of each input list.  
-- • It is exactly the prefix of both str1 and str2.  
-- • It is empty if the first characters of the inputs differ or if one of the lists is empty.
--
-- -----Note-----  
-- It is assumed that both inputs are provided as valid lists of characters. The function always returns the correct longest common prefix based on the inputs.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
  -- !benchmark @start code
  let minLength := Nat.min str1.length str2.length
  let rec aux (idx : Nat) (acc : List Char) : List Char :=
    if idx < minLength then
      match str1[idx]?, str2[idx]? with
      | some c1, some c2 =>
          if c1 ≠ c2 then acc
          else aux (idx + 1) (acc ++ [c1])
      | _, _ => acc
    else acc
  aux 0 []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :=
  -- !benchmark @start postcond
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem LongestCommonPrefix_spec_satisfied (str1: List Char) (str2: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    LongestCommonPrefix_postcond (str1) (str2) (LongestCommonPrefix (str1) (str2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

