-- -----Description-----
-- This task requires writing a Lean 4 method that determines whether an array of integers contains only one distinct element. The method should return true if the array is empty or if every element in the array is the same, and false if there are at least two different elements.
--
-- -----Input-----
-- The input consists of:
-- a: An array of integers.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the array is empty or if all elements in the array are identical.
-- Returns false if the array contains at least two distinct elements.
--
-- -----Note-----
-- The input array is assumed to be non-null.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  -- !benchmark @start code
  if a.size = 0 then
    true
  else
    let firstElement := a[0]!
    let rec loop (i : Nat) : Bool :=
      if h : i < a.size then
        if a[i]! = firstElement then loop (i + 1) else false
      else
        true
    loop 1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) (h_precond : hasOnlyOneDistinctElement_precond (a)) :=
  -- !benchmark @start postcond
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasOnlyOneDistinctElement_spec_satisfied (a: Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    hasOnlyOneDistinctElement_postcond (a) (hasOnlyOneDistinctElement (a) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop
  -- !benchmark @end proof
