-- -----Description-----
-- This task requires writing a Lean 4 method that removes an element from a given array of integers at a specified index. The resulting array should contain all the original elements except for the one at the given index. Elements before the removed element remain unchanged, and elements after it are shifted one position to the left.
--
-- -----Input-----
-- The input consists of:
-- • s: An array of integers.
-- • k: A natural number representing the index of the element to remove (0-indexed).
--
-- -----Output-----
-- The output is an array of integers that:
-- • Has a length one less than the input array.
-- • Contains the same elements as the input array, except that the element at index k is omitted.
-- • Preserves the original order with elements after the removed element shifted left by one position.
--
-- -----Note-----
-- It is assumed that k is a valid index (0 ≤ k < the length of the array).

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
namespace tmp
@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k < s.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  -- !benchmark @start code
  s.eraseIdx! k
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  -- !benchmark @start postcond
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem removeElement_spec_satisfied (s: Array Int) (k: Nat) (h_precond : removeElement_precond (s) (k)) :
    removeElement_postcond (s) (k) (removeElement (s) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic?
  -- !benchmark @end proof
end tmp
