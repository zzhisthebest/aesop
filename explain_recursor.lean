import Codetic

-- 递归器（recursor）是归纳类型的核心证明原理

-- 对于List，Lean自动生成的标准递归器
#check @List.recOn
-- List.recOn : {α : Type u_1} → {motive : List α → Sort u_2} →
--   (t : List α) → motive [] → ((head : α) → (tail : List α) → motive tail → motive (head :: tail)) → motive t
-- 意思：要证明某个性质对所有List成立，需要：
-- 1. 证明它对 [] 成立
-- 2. 证明如果它对 tail 成立，那么对 head :: tail 也成立

-- 我们自定义的反向递归器
#check @List.reverseRecOn
-- List.reverseRecOn : {α : Type u} → {motive : List α → Sort v} →
--   (l : List α) → motive [] → ((l : List α) → (a : α) → motive l → motive (l ++ [a])) → motive l
-- 意思：要证明某个性质对所有List成立，需要：
-- 1. 证明它对 [] 成立
-- 2. 证明如果它对 l 成立，那么对 l ++ [a] 也成立（从右边添加元素）

-- 示例：用标准归纳法
example (l : List Nat) : l.length = l.length := by
  induction l  -- 使用 List.recOn，产生两个case：nil 和 cons
  case nil => rfl
  case cons head tail ih => rfl

-- 示例：用反向归纳法（需要手动指定）
example (l : List Nat) : l.reverse.reverse = l := by
  -- 在标准Lean中写法是：induction l using List.reverseRecOn
  -- 这会使用 List.reverseRecOn 作为递归器
  -- 产生两个case：nil 和 append_singleton
  sorry
