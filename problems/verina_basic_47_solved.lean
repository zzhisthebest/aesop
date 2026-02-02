-- -----Description-----
-- This task requires writing a Lean 4 method that calculates the sum of all the elements in an array of integers. The method should process the entire array and return the total sum of its elements.
--
-- -----Input-----
-- The input consists of:
-- a: An array of integers.
--
-- -----Output-----
-- The output is an integer:
-- Returns the sum of all elements in the input array.
--
-- -----Note-----
-- - The input array is assumed not to be null.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
--import Mathlib
import Codetic
namespace tmp
@[reducible, simp]
def arraySum_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  -- !benchmark @start code
  a.toList.sum
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!
-- !benchmark @end postcond_aux


@[reducible, simp]
def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  -- !benchmark @start postcond
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size
  -- !benchmark @end postcond


-- !benchmark @start proof_aux
theorem eq_of_sub_zero_and_ge (a b : Int) : a = b → a - b = 0 ∧ a ≥ b := by
  omega
-- !benchmark @end proof_aux
--这个题目可能带来突破！
theorem arraySum_spec_satisfied (a: Array Int) (h_precond : arraySum_precond (a)) :
    arraySum_postcond (a) (arraySum (a) h_precond) h_precond := by
  -- !benchmark @start proof
  --codetic
  unfold arraySum arraySum_postcond
  apply eq_of_sub_zero_and_ge a.toList.sum (sumTo a a.size)--这个定理很有用
  cases a with | mk d =>--还是把Array转为List
    simp
    induction d with--数学归纳法
    | nil => unfold sumTo;codetic
    | cons x xs ih =>--ih在最后用到了
      unfold sumTo
      simp
      cases xs with
      | nil => unfold sumTo;simp
      | cons y ys =>
        --unfold sumTo
        --codetic
        rw [ih]
        · have h3 (x' : Int) (xs' : List Int): xs'.length ≠ 0 → sumTo ⟨x'::xs'⟩ xs'.length = x' + sumTo ⟨xs'⟩ (xs'.length - 1) := by--命名很显然，但就是必须数学归纳法证明
            --codetic
            --竟然还能对List.length归纳
            induction xs'.length with
            | zero => unfold sumTo;codetic
            | succ n ih_len =>
              unfold sumTo
              codetic

          have h4 : sumTo ⟨x::y::ys⟩ (ys.length + 1) = x + sumTo ⟨y::ys⟩ ys.length := by
          --grind
            codetic--用到了h3
          --rw [sumTo]
          rw [sumTo]--还真不能unfold，unfold是在两侧，而rw只在第一个地方
          codetic
        · codetic
  -- !benchmark @end proof
--己
#check Int.add_assoc
