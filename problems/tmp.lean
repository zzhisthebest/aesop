import Aesop
set_option maxHeartbeats 0

namespace test

-- 测试：对不同变量的 induction 是否都能尝试
theorem test_two_lists (xs ys : List Nat) :
    xs ++ ys = xs ++ ys := by
  aesop?

theorem test_nat_list (n : Nat) (xs : List Nat) :
    n + xs.length = n + xs.length := by
  aesop?

end test
