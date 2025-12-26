-- -----Description-----
-- This task requires writing a Lean 4 method that returns the smallest natural number missing from a given sorted list of natural numbers. In other words, starting from 0, the method should identify the first natural number that does not appear in the list. The input list is assumed to be sorted in non-decreasing order and contains only natural numbers (including 0).
--
-- -----Input-----
-- The input consists of:
-- s: A list of natural numbers sorted in non-decreasing order.
--
-- -----Output-----
-- The output is a natural number:
-- Returns the smallest natural number that does not appear in the input list.
--
-- -----Note-----
-- It is assumed that the input list is sorted and contains only natural numbers.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def smallestMissingNumber_precond (s : List Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) s
  -- !benchmark @end precond

-- !benchmark @start code_aux

-- !benchmark @end code_aux


def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  -- !benchmark @start code
  let rec findMissing (v : Nat) (l : List Nat) : Nat :=
    match l with
    | [] => v
    | x :: xs =>
      if x > v then v
      else if x = v then findMissing (v + 1) xs
      else findMissing v xs
  findMissing 0 s
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def smallestMissingNumber_postcond (s : List Nat) (result: Nat) (h_precond : smallestMissingNumber_precond (s)) :=
  -- !benchmark @start postcond
  ¬ List.elem result s ∧ (∀ k : Nat, k < result → List.elem k s)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

theorem findMissing_ge_v (v : Nat) (l : List Nat) :
    v ≤ smallestMissingNumber.findMissing v l := by
  induction v, l using smallestMissingNumber.findMissing.induct with
  | case1 v => simp [smallestMissingNumber.findMissing]
  | case2 v x xs h_gt =>
    simp [smallestMissingNumber.findMissing, h_gt]
  | case3 v x xs h_le =>
    sorry
  | case4 v x xs h_le h_ne ih =>
    simp [smallestMissingNumber.findMissing, h_le, h_ne]
    exact ih

theorem smallestMissingNumber_spec_satisfied (s: List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    smallestMissingNumber_postcond (s) (smallestMissingNumber (s) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold smallestMissingNumber smallestMissingNumber_postcond
  unfold smallestMissingNumber_precond at h_precond
  constructor
  · -- 将 Bool 类型的 elem 转换成 Prop 类型的 ∉ (not mem)
    --rw [List.elem_eq_false_iff]

    -- 泛化变量 v，并增加“v 是下界”的约束
    let v := 0
    have h_lower : ∀ y ∈ s, v ≤ y := by aesop

    -- 开始函数归纳
    induction v, s using smallestMissingNumber.findMissing.induct with
    | case1 v =>
      simp [smallestMissingNumber.findMissing]
    | case2 v x xs h_gt =>
      -- 此时 x > v。由于列表有序且 x 是头，所以 v 必定小于列表里所有元素
      simp [smallestMissingNumber.findMissing, h_gt]
      aesop
    | case3 v x xs h_le =>
      -- 此时 x = v，递归寻找 v + 1
      simp [smallestMissingNumber.findMissing]
      sorry
      --aesop
    | case4 v x xs h_le h_ne ih =>
      -- 此时 x < v。这在有序且 v 是下界的情况下其实是矛盾的
      simp [smallestMissingNumber.findMissing]

      sorry
      --aesop
  · sorry

  -- !benchmark @end proof
