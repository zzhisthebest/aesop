-- -----Description-----
-- This task requires writing a Lean 4 method that extracts even numbers from an array of integers. The method should return a new array containing only the even numbers found in the input array, while preserving the order in which they appear.
--
-- -----Input-----
-- The input consists of:
-- arr: An array of integers.
--
-- -----Output-----
-- The output is an array of integers:
-- Returns an array containing all the even numbers from the input array. Specifically:
-- - Every element in the output array is an even integer.
-- - All even integers present in the input array are included in the output array.
-- - The relative order of the even integers is preserved as in the input array.
--
-- -----Note-----
-- There are no preconditions for this task; the method will work with any array, including empty arrays (which are not null).

-- !benchmark @start import type=solution

-- !benchmark @end import
import Codetic
namespace tmp
-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  -- !benchmark @start code
  arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  -- !benchmark @start postcond
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux
/--
  核心引理：证明通过 foldl 筛选出的元素一定满足 isEven 条件。
  这里使用 generalizing acc 来确保归纳过程中累加器的状态是可变的。
-/
theorem isEven_of_mem_foldl_filter {α : Type} [Inhabited α] (d : List Int) (x : Int) (acc : Array Int) :
    (∀ a ∈ acc.toList, isEven a = true) →
    x ∈ (d.foldl (fun acc y => if isEven y = true then acc.push y else acc) acc).toList →
    isEven x = true := by
  -- 对列表 d 进行归纳
  induction d generalizing acc with
  | nil =>
    -- 基础情况：列表为空，x 必然已经在初始的 acc 中
    intro h_acc_even h_mem
    simp at h_mem
    exact h_acc_even x h_mem
  | cons y ys ih =>
    -- 归纳步骤：处理头元素 y
    intro h_acc_even h_mem
    simp at h_mem
    -- 反向 split：模拟代码中的 if-then-else
    split at h_mem
    · -- 情况 1：isEven y = true，y 被推入 acc
      next h_y_even =>
        apply ih (acc.push y) _ h_mem
        -- 证明新的 acc (即 acc + y) 里的元素全都是偶数
        intro a ha
        simp at ha
        rcases ha with ha | ha
        · rwa [ha] -- 元素是 y 本身
        · exact h_acc_even a ha -- 元素在旧的 acc 中
    · -- 情况 2：isEven y = false，acc 保持不变
      next h_y_odd =>
        apply ih acc h_acc_even h_mem

theorem findEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    findEvenNumbers_postcond (arr) (findEvenNumbers (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findEvenNumbers_postcond findEvenNumbers
  clear h_precond
  simp
  constructor
  · --这是一个spec
    intro x h1
    cases arr with | mk d =>
      constructor
      · -- 在你的主证明中
        rw [Array.foldl_eq_foldl_toList]
        apply isEven_of_mem_foldl_filter

        simp at h1
      · sorry
  constructor
  · --这是一个spec
    sorry
  · --这是一个spec
    sorry

  -- !benchmark @end proof
#check Array.foldl
