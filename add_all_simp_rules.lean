/-
这个文件展示了如何批量将 Lean 自带的所有定理添加到 codetic 的 simp ruleset

注意：直接添加所有定理可能会导致性能问题。建议：
1. 只添加常用的定理
2. 按命名空间分组添加
3. 使用默认的 simp set（已经包含所有 @[simp] 标记的定理）
-/
import Codetic
import Lean.Meta.Tactic.Simp.Types

namespace AddAllSimpRules

-- 声明一个自定义 ruleset 用于存放所有 Lean 定理
declare_codetic_rule_sets [all_lean_theorems]

-- 方法 1: 手动添加常用的 Lean 定理到 simp ruleset
-- 这是最安全和可控的方法
attribute [codetic (rule_sets := [all_lean_theorems]) norm simp]
  Nat.add_comm Nat.add_assoc Nat.add_zero Nat.zero_add
  Nat.mul_comm Nat.mul_assoc Nat.mul_one Nat.one_mul
  Nat.mul_zero Nat.zero_mul
  List.length_cons List.length_nil
  List.append_nil List.nil_append

-- 方法 2: 使用宏批量添加特定命名空间的定理
-- 注意：这需要在编译时知道所有要添加的定理名称
macro "add_nat_simp_rules" : command => `(
  attribute [codetic (rule_sets := [all_lean_theorems]) norm simp]
    Nat.add_comm Nat.add_assoc Nat.add_zero Nat.zero_add
    Nat.mul_comm Nat.mul_assoc Nat.mul_one Nat.one_mul
    Nat.mul_zero Nat.zero_mul Nat.add_left_comm Nat.mul_left_comm
    Nat.succ_eq_add_one Nat.add_succ
)

macro "add_list_simp_rules" : command => `(
  attribute [codetic (rule_sets := [all_lean_theorems]) norm simp]
    List.length_cons List.length_nil List.length_append
    List.append_nil List.nil_append List.append_assoc
)

-- 使用示例
add_nat_simp_rules
add_list_simp_rules

-- 现在可以在 codetic 中使用这个 ruleset
example {a b c : Nat} : (a + b) + c = a + (b + c) := by
  codetic (rule_sets := [all_lean_theorems])

example {a b : Nat} : a + b = b + a := by
  codetic (rule_sets := [all_lean_theorems])

-- 方法 3: 如果你想使用所有已经标记为 @[simp] 的定理
-- codetic 默认已经启用了 useDefaultSimpSet := true
-- 这意味着所有 @[simp] 标记的定理都可以被 codetic 使用
-- 你只需要确保 useDefaultSimpSet 没有被禁用

example {a b : Nat} : a + 0 = a := by
  -- 这会使用默认的 simp set，包括所有 @[simp] 标记的定理
  codetic

end AddAllSimpRules
