-- -----Description-----  
-- Determine whether two strings match based on a specific pattern: for each position in the strings, either the characters are the same, or the character in p is a wildcard represented by a question mark '?' that may match any character.
--
-- -----Input-----  
-- The input consists of:  
-- • s: A string that is to be matched.  
-- • p: A pattern string of equal length, where each character is either a specific character or the wildcard '?'.
--
-- -----Output-----  
-- The output is a Boolean value:  
-- • Returns true if the length of s is equal to the length of p and each corresponding character in s and p are either identical or the character in p is a '?'.  
-- • Returns false if any character in s does not match the corresponding character in p and the character in p is not a '?'.
--
-- -----Note-----  
-- It is assumed that both strings provided have the same length.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Match_precond (s : String) (p : String) : Prop :=
  -- !benchmark @start precond
  s.toList.length = p.toList.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  -- !benchmark @start code
  let sList := s.toList
  let pList := p.toList
  let rec loop (i : Nat) : Bool :=
    if i < sList.length then
      if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
      else loop (i + 1)
    else true
  loop 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Match_postcond (s : String) (p : String) (result: Bool) (h_precond : Match_precond (s) (p)) :=
  -- !benchmark @start postcond
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Match_spec_satisfied (s: String) (p: String) (h_precond : Match_precond (s) (p)) :
    Match_postcond (s) (p) (Match (s) (p) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

