-- -----Description-----
-- This task involves taking an array as input and producing a new array that has the same size and identical elements in the same order as the input.
--
-- -----Input-----
-- The input consists of:
-- • s: An array of elements (for testing purposes, assume an array of integers, i.e., Array Int).
--
-- -----Output-----
-- The output is an array of the same type as the input:
-- • The output array has the same size as the input array.
-- • Each element in the output array is identical to the corresponding element in the input array.
--
-- -----Note-----
-- There are no special preconditions for the input array (it can be empty or non-empty); the function simply performs a straightforward copy operation on the array.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
@[reducible, simp]
def iter_copy_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc  -- This case shouldn't happen when i < s.size
    else
      acc
  loop 0 Array.empty
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def iter_copy_postcond (s : Array Int) (result: Array Int) (h_precond : iter_copy_precond (s)) :=
  -- !benchmark @start postcond
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem iter_copy_spec_satisfied (s: Array Int) (h_precond : iter_copy_precond (s)) :
    iter_copy_postcond (s) (iter_copy (s) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold iter_copy_postcond iter_copy
  constructor
  · --这是一个spec
    cases s with | mk d =>--还是把Array转为List
      codetic
      simp
      induction d with--数学归纳法,对列表进行数学归纳
      | nil=>
        unfold iter_copy.loop
        simp
        trivial
      | cons x xs ih =>
        unfold iter_copy.loop
        simp
        --codetic
        sorry

  · --这是一个spec
    cases s with | mk d =>--还是把Array转为List
      simp
      induction d with--数学归纳法,对列表进行数学归纳
      | nil=>
        unfold iter_copy.loop
        simp
      | cons x xs ih =>
        unfold iter_copy.loop
        simp
        codetic
        sorry
  -- !benchmark @end proof
