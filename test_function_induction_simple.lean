import Aesop
set_option trace.aesop.zzh_custom true

namespace test

def foo_aux (n : Nat) (acc : Nat) : Nat :=
  if n = 0 then
    acc
  else
    foo_aux (n - 1) (acc + 1)

-- 这个定理的目标包含 foo_aux 调用
-- Aesop 应该检测到并添加函数归纳规则
theorem test_detection (n acc : Nat) :
    foo_aux n acc = acc + n := by
  sorry -- 只测试规则是否被添加，不完成证明

end test




