/-
这个文件展示了如何让 aesop 使用更多定理的几种方法
-/
import Aesop

namespace AesopAllTheorems

-- 方法 1: 在调用时添加多个规则
example {a b : Nat} : a + b = b + a := by
  aesop (add safe [Nat.add_comm, Nat.add_assoc, Nat.add_zero])

-- 方法 2: 全局注册规则到 default ruleset
-- 这样所有 aesop 调用都可以使用这些规则
attribute [aesop safe] Nat.add_comm
attribute [aesop safe] Nat.add_assoc
attribute [aesop norm simp] Nat.add_zero

-- 现在可以直接使用
example {a b : Nat} : a + b = b + a := by
  aesop

-- 方法 3: 创建一个自定义 ruleset 包含更多规则
declare_aesop_rule_sets [nat_rules]

-- 将规则添加到自定义 ruleset
attribute [aesop (rule_sets := [nat_rules]) safe] Nat.add_comm
attribute [aesop (rule_sets := [nat_rules]) safe] Nat.add_assoc
attribute [aesop (rule_sets := [nat_rules]) norm simp] Nat.mul_comm

-- 使用自定义 ruleset
example {a b : Nat} : a + b = b + a := by
  aesop (rule_sets := [nat_rules])

-- 方法 4: 批量添加常用 Nat 定理
-- 可以创建一个宏或函数来批量注册
macro "add_nat_rules" : tactic => `(tactic|
  aesop (add safe [Nat.add_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_assoc]))

example {a b c : Nat} : (a + b) + c = a + (b + c) := by
  add_nat_rules

-- 方法 5: 使用 unsafe apply 规则来尝试所有可能的定理
-- 注意：这会大大增加搜索空间，可能导致性能问题
example {a b : Nat} : a + b = b + a := by
  aesop (add unsafe 10% apply Nat.add_comm)

end AesopAllTheorems
