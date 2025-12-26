-- -----Description-----
-- You are given an array of integers and a threshold value k. The problem is to create a new array where every element greater than k is replaced with -1 while every other element remains unchanged.
--
-- -----Input-----
-- The input consists of:
-- • arr: An array of integers.
-- • k: An integer used as the threshold for replacement.
--
-- -----Output-----
-- The output is an array of integers that satisfies the following conditions:
-- • For every index i, if arr[i] is greater than k, then the returned array at index i is -1.
-- • For every index i, if arr[i] is less than or equal to k, then the returned array at index i remains unchanged.
--
-- -----Note-----
-- It is assumed that the input array may be empty or non-empty, and that k can be any integer. There are no additional preconditions.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Mathlib
@[reducible, simp]
def replace_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc
-- !benchmark @end code_aux


def replace (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  -- !benchmark @start code
  replace_loop arr k 0 arr
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def replace_postcond (arr : Array Int) (k : Int) (result: Array Int) (h_precond : replace_precond (arr) (k)) :=
  -- !benchmark @start postcond
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
  (∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem replace_spec_satisfied (arr: Array Int) (k: Int) (h_precond : replace_precond (arr) (k)) :
    replace_postcond (arr) (k) (replace (arr) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold replace replace_postcond
  constructor
  intro i
  intro h1 h2
  induction i
  · sorry
  · rename_i n h3
    unfold replace_loop
    split_ifs


  -- simp_all
  -- constructor
  -- · intro i h1 h2
  --   split_ifs with h3 h4
  --   sorry
  --   sorry
  --   sorry
  -- · sorry
  -- !benchmark @end proof
