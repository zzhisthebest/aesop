import Mathlib
import Codetic
#check List.reverseRecOn

theorem reverse_sandwich (l : List α) (a : α) :
  ( [a] ++ l ++ [a] ).reverse = [a] ++ l.reverse ++ [a] := by
  -- 请使用 List.reverseRecOn l ... 开始你的证明
  induction l using List.reverseRecOn with
  | nil =>
    -- 基础情况：l = []
    simp
  | append_singleton l' x ih =>
    -- 归纳步骤：假设 l' 成立，证明 l' ++ [x] 成立
    simp
    -- 剩下的交给 simp 或 rw [ih]
    sorry
