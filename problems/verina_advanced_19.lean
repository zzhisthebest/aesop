-- -----Description-----
-- This task requires writing a Lean 4 method that checks whether a given string is a palindrome. A palindrome is a string that reads the same forwards and backwards. The function should ignore whitespace, punctuation, and capitalization when checking for palindromes.
--
-- -----Input-----
-- The input consists of:
-- s: A string to be checked.
--
-- -----Output-----
-- The output is a boolean:
-- Returns true if the input string is a palindrome when non-alphabetic characters are removed and letters are treated case-insensitively, and false otherwise.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import
import Aesop
namespace tmp
-- !benchmark @start solution_aux
-- Check if a character is an uppercase alphabet letter
def isUpperAlpha (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

-- Check if a character is a lowercase alphabet letter
def isLowerAlpha (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

-- Determine if a character is alphabetic
def isAlpha (c : Char) : Bool :=
  isUpperAlpha c ∨ isLowerAlpha c

-- Convert a single character to lowercase
def toLower (c : Char) : Char :=
  if isUpperAlpha c then Char.ofNat (c.toNat + 32) else c

-- Normalize a character: keep only lowercase letters
def normalizeChar (c : Char) : Option Char :=
  if isAlpha c then some (toLower c) else none

-- Normalize a string into a list of lowercase alphabetic characters
def normalizeString (s : String) : List Char :=
  s.toList.foldr (fun c acc =>
    match normalizeChar c with
    | some c' => c' :: acc
    | none    => acc
  ) []
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isCleanPalindrome_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- Reverse the list
def reverseList (xs : List Char) : List Char :=
  xs.reverse
-- !benchmark @end code_aux


def isCleanPalindrome (s : String) (h_precond : isCleanPalindrome_precond (s)) : Bool :=
  -- !benchmark @start code
  let norm := normalizeString s
  norm = reverseList norm
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def isCleanPalindrome_postcond (s : String) (result: Bool) (h_precond : isCleanPalindrome_precond (s)) : Prop :=
  -- !benchmark @start postcond
  let norm := normalizeString s
  (result = true → norm = norm.reverse) ∧
  (result = false → norm ≠ norm.reverse)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isCleanPalindrome_spec_satisfied (s: String) (h_precond : isCleanPalindrome_precond (s)) :
    isCleanPalindrome_postcond (s) (isCleanPalindrome (s) h_precond) h_precond := by
  -- !benchmark @start proof
  --simp [isCleanPalindrome_postcond ,isCleanPalindrome] at *
  aesop?--(config:={useSimpAll:=false})
  unfold isCleanPalindrome_postcond isCleanPalindrome
  simp
  constructor
  · --这是一个spec
    unfold reverseList
    simp
  · --这是一个spec
    unfold reverseList
    simp
  -- !benchmark @end proof

--之所以简单，是因为spec用的是code里的函数，并且这里的code本身也简单
--己
