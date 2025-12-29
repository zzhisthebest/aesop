-- -----Description-----
-- This task requires writing a Lean 4 method that determines whether one list is a sublist of another. In other words, the method should check if the first list appears as a contiguous sequence within the second list and return true if it does, and false otherwise.
--
-- -----Input-----
-- The input consists of two lists of integers:
-- sub: A list of integers representing the potential sublist.
-- main: A list of integers in which to search for the sublist.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the first list appears as a contiguous sequence within the second list.
-- Returns false if the first list does not appear as a contiguous sequence in the second list.
--
-- -----Note-----
-- There are no preconditions for this method; the sequences are always non-null.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  -- !benchmark @start code
  let subLen := sub.length
  let mainLen := main.length
  if subLen > mainLen then
    false
  else
    let rec check (i : Nat) : Bool :=
      if i + subLen > mainLen then
        false
      else if sub = (main.drop i).take subLen then
        true
      else if i + 1 ≤ mainLen then
        check (i + 1)
      else
        false
    termination_by mainLen - i
    check 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isSublist_postcond (sub : List Int) (main : List Int) (result: Bool) (h_precond : isSublist_precond (sub) (main)) :=
  -- !benchmark @start postcond
  (∃ i, i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isSublist_spec_satisfied (sub: List Int) (main: List Int) (h_precond : isSublist_precond (sub) (main)) :
    isSublist_postcond (sub) (main) (isSublist (sub) (main) h_precond) h_precond := by
  -- !benchmark @start proof
 -- aesop
  unfold isSublist_postcond isSublist
  simp
  constructor
  · intro h1
    rcases h1 with ⟨i, h1, h2⟩
    constructor
    · grind
    · unfold isSublist.check
      simp
      constructor
      grind


  · intro h1
    rcases h1 with ⟨h1,h2⟩

    sorry


  -- !benchmark @end proof
--不会
