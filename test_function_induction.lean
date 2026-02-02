import Codetic

namespace test

-- 定义一个递归函数
def sum_aux (n : Nat) (acc : Nat) : Nat :=
  if n = 0 then
    acc
  else
    sum_aux (n - 1) (acc + n)

def sum (n : Nat) : Nat :=
  sum_aux n 0

-- 测试：函数归纳应该被自动检测和应用
theorem sum_aux_spec (n : Nat) (acc : Nat) :
    sum_aux n acc = acc + n * (n + 1) / 2 := by
  -- Codetic 应该自动检测到 sum_aux 的调用，并尝试应用函数归纳
  codetic?

end test




