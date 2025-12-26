-- -----Description-----
-- This task requires writing a Lean 4 method that removes all occurrences of a given element from a list of natural numbers. The method should return a new list that contains all the elements of the original list except those equal to the target number. The order of the remaining elements must be preserved.
--
-- -----Input-----
-- The input consists of two elements:
-- lst: A list of natural numbers (List Nat).
-- target: A natural number to be removed from the list.
--
-- -----Output-----
-- The output is a list of natural numbers:
-- Returns a new list with all occurrences of the target number removed. The relative order of the remaining elements must be the same as in the input list.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  -- !benchmark @start code
  let rec helper (lst : List Nat) (target : Nat) : List Nat :=
    match lst with
    | [] => []
    | x :: xs =>
      let rest := helper xs target
      if x = target then rest else x :: rest
  helper lst target
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat) (h_precond : removeElement_precond (lst) (target)): Prop :=
  -- !benchmark @start postcond
  -- 1. All elements equal to target are removed from the result.
  -- 2. All other elements are preserved in order.
  -- 3. No new elements are added.

  -- Helper predicate: result contains exactly the elements of lst that are not equal to target, in order
  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux
-- !benchmark @end proof_aux


theorem removeElement_spec_satisfied (lst: List Nat) (target: Nat) (h_precond : removeElement_precond (lst) (target)):
    removeElement_postcond (lst) (target) (removeElement (lst) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

