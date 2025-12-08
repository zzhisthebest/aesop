/-
批量添加 Lean 自带定理到 aesop 的 simp ruleset

重要说明：
1. aesop 默认已经使用所有 @[simp] 标记的定理（useDefaultSimpSet := true）
2. 如果你想要使用没有 @[simp] 标记的定理，需要手动添加
3. 直接添加所有定理会导致性能问题，建议按需添加
-/
import Aesop

namespace BatchAddSimpRules

-- 创建一个自定义 ruleset 用于存放所有 Lean 定理
declare_aesop_rule_sets [lean_all_theorems]

-- 方法 1: 批量添加 Nat 相关的常用定理
attribute [aesop (rule_sets := [lean_all_theorems]) norm simp]
  -- 加法相关
  Nat.add_comm Nat.add_assoc Nat.add_zero Nat.zero_add
  Nat.add_left_comm Nat.add_right_comm
  Nat.succ_eq_add_one Nat.add_succ
  -- 乘法相关
  Nat.mul_comm Nat.mul_assoc Nat.mul_one Nat.one_mul
  Nat.mul_zero Nat.zero_mul Nat.mul_left_comm
  -- 减法和比较
  Nat.sub_zero Nat.zero_sub Nat.sub_self
  Nat.le_refl Nat.lt_irrefl

-- 方法 2: 批量添加 List 相关的常用定理
attribute [aesop (rule_sets := [lean_all_theorems]) norm simp]
  List.length_cons List.length_nil List.length_append
  List.append_nil List.nil_append List.append_assoc
  List.map_nil List.map_cons List.map_append

-- 方法 3: 批量添加 Bool 相关的常用定理
attribute [aesop (rule_sets := [lean_all_theorems]) norm simp]
  Bool.not_true Bool.not_false Bool.and_true Bool.true_and
  Bool.and_false Bool.false_and Bool.or_true Bool.true_or
  Bool.or_false Bool.false_or

-- 方法 4: 批量添加 Option 相关的常用定理
attribute [aesop (rule_sets := [lean_all_theorems]) norm simp]
  Option.map_none Option.map_some

-- 使用示例
example {a b c : Nat} : (a + b) + c = a + (b + c) := by
  aesop (rule_sets := [lean_all_theorems])

example {a b : Nat} : a + b = b + a := by
  aesop (rule_sets := [lean_all_theorems])

example {xs ys : List Nat} : (xs ++ ys).length = xs.length + ys.length := by
  aesop (rule_sets := [lean_all_theorems])

-- 方法 5: 如果你想在每次调用时都使用这个 ruleset，
-- 可以将其设置为默认 ruleset（需要修改初始化代码）
-- 或者创建一个宏来简化调用

macro "aesop_all" : tactic => `(tactic| aesop (rule_sets := [lean_all_theorems]))

example {a b : Nat} : a + b = b + a := by
  aesop_all

end BatchAddSimpRules
