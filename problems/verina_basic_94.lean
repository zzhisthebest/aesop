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
import Aesop
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
  simp [iter_copy, iter_copy_postcond]

  -- 定义循环不变式并证明辅助递归函数
  let rec loop_property (i : Nat) (acc : Array Int)
    (h_acc : acc.size = i ∧ ∀ j < i, acc[j]! = s[j]!) :
    let res := iter_copy.loop s i acc
    res.size = s.size ∧ ∀ j < s.size, res[j]! = s[j]! := by

    -- 处理递归终止情况
    if h_lt : i < s.size then
      have h_idx : i < s.size := h_lt
      -- 展开一步递归
      unfold iter_copy.loop
      simp [h_lt]

      -- 处理数组访问
      match h_val : s[i]? with
      | some val =>
        -- 证明 push 后的新数组依然满足不变式
        have h_eq_val : s[i]! = val := by
          simp [Array.getElem!_eq_getElem?_getD, h_val]

        let next_acc := acc.push val
        have next_h_acc : next_acc.size = i + 1 ∧ ∀ j < i + 1, next_acc[j]! = s[j]! := by
          constructor
          · simp [next_acc, h_acc.1]
          · intro j hj
            if h_j_lt : j < i then
              -- 之前的元素保持不变
              have : next_acc[j]! = acc[j]! := by
                simp [next_acc, Array.getElem!_pos, h_j_lt, h_acc.1]
              rw [this, h_acc.2 j h_j_lt]
            else
              -- 新 push 的元素
              have h_j_eq : j = i := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) (Nat.not_lt_iff_le.mp h_j_lt)
              simp [h_j_eq, next_acc, h_acc.1, h_eq_val]

        -- 递归调用
        exact loop_property (i + 1) next_acc next_h_acc
      | none =>
        -- 矛盾情况：i < s.size 但 s[i]? 为 none
        have := Array.getElem?_eq_none_iff.mp h_val
        absurd h_lt; exact Nat.not_lt_of_le this
    else
      -- 递归结束：i >= s.size
      unfold iter_copy.loop
      simp [h_lt]
      have h_i_eq : i = s.size := Nat.le_antisymm (Nat.not_lt_iff_le.mp h_lt) (by
        -- 这里需要通过归纳保证 i 不会超过 s.size
        -- 在实际证明中，我们需要在 loop_property 中添加 i <= s.size 的约束
        sorry
      )
      rw [← h_i_eq]
      exact h_acc

  -- 调用初始状态：i=0, acc=empty
  apply loop_property 0 Array.empty
  simp


  -- !benchmark @start proof
  unfold iter_copy_postcond iter_copy
  constructor
  · --这是一个spec
    cases s with | mk d =>--还是把Array转为List
      simp
      induction d with--数学归纳法,对列表进行数学归纳
      | nil=>
        unfold iter_copy.loop
        simp
        trivial
      | cons x xs ih =>
        unfold iter_copy.loop
        simp
        --aesop
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
        aesop
        sorry
  -- !benchmark @end proof
