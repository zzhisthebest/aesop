/-
这个文件展示了如何让 codetic 使用更多定理的几种方法
-/
import Codetic

namespace CodeticAllTheorems

-- 方法 1: 在调用时添加多个规则
example {a b : Nat} : a + b = b + a := by
  codetic (add safe [Nat.add_comm, Nat.add_assoc, Nat.add_zero])

-- 方法 2: 全局注册规则到 default ruleset
-- 这样所有 codetic 调用都可以使用这些规则
attribute [codetic safe] Nat.add_comm
attribute [codetic safe] Nat.add_assoc
attribute [codetic norm simp] Nat.add_zero

-- 现在可以直接使用
example {a b : Nat} : a + b = b + a := by
  codetic

-- 方法 3: 创建一个自定义 ruleset 包含更多规则
declare_codetic_rule_sets [nat_rules]

-- 将规则添加到自定义 ruleset
attribute [codetic (rule_sets := [nat_rules]) safe] Nat.add_comm
attribute [codetic (rule_sets := [nat_rules]) safe] Nat.add_assoc
attribute [codetic (rule_sets := [nat_rules]) norm simp] Nat.mul_comm

-- 使用自定义 ruleset
example {a b : Nat} : a + b = b + a := by
  codetic (rule_sets := [nat_rules])

-- 方法 4: 批量添加常用 Nat 定理
-- 可以创建一个宏或函数来批量注册
macro "add_nat_rules" : tactic => `(tactic|
  codetic (add safe [Nat.add_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_assoc]))

example {a b c : Nat} : (a + b) + c = a + (b + c) := by
  add_nat_rules

-- 方法 5: 使用 unsafe apply 规则来尝试所有可能的定理
-- 注意：这会大大增加搜索空间，可能导致性能问题
example {a b : Nat} : a + b = b + a := by
  codetic (add unsafe 10% apply Nat.add_comm)

end CodeticAllTheorems
