-- -----Description-----
-- This task requires writing a Lean 4 method that calculates the product of all distinct integers in an array. The method should consider each unique integer only once when computing the product and return the resulting value. If the array is empty, the method should return 1.
--
-- -----Input-----
-- The input consists of:
-- arr: An array of integers.
--
-- -----Output-----
-- The output is an integer:
-- Returns the product of all unique integers from the input array.
--
-- -----Note-----
-- The order in which the unique integers are multiplied does not affect the final product.

-- !benchmark @start import type=solution
import Codetic
namespace tmp
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def uniqueProduct_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (seen : Std.HashSet Int) (product : Int) : Int :=
    if i < arr.size then
      let x := arr[i]!
      if seen.contains x then
        loop (i + 1) seen product
      else
        loop (i + 1) (seen.insert x) (product * x)
    else
      product
  loop 0 Std.HashSet.empty 1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def uniqueProduct_postcond (arr : Array Int) (result: Int) (h_precond : uniqueProduct_precond (arr)) :=
  -- !benchmark @start postcond
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0
  -- !benchmark @end postcond



-- !benchmark @start proof_aux

-- !benchmark @end proof_aux
#check uniqueProduct.loop.induct

theorem uniqueProduct_spec_satisfied (arr: Array Int) (h_precond : uniqueProduct_precond (arr)) :
    uniqueProduct_postcond (arr) (uniqueProduct (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold uniqueProduct_postcond uniqueProduct
  simp_all
  rw [Int.sub_eq_zero]
  rw [Int.sub_eq_zero]
  rw [eq_comm]
  simp
  apply uniqueProduct.loop.induct

  -- 将 a ≤ b ∧ b ≤ a 转换为 a = b,
  --两个spec等价，本质上是一个spec
  cases arr with | mk d =>--还是把Array转为List

    simp
    induction d with--数学归纳法
    | nil => unfold uniqueProduct.loop;simp
    | cons x xs ih =>--ih在最后用到了
      unfold uniqueProduct.loop
      simp

      by_cases h1:x∈xs
      ·




  -- !benchmark @end proof
#check List.foldl
--不会证明
