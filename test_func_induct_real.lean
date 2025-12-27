import Aesop
set_option trace.aesop.zzh_custom true
set_option maxHeartbeats 100000

namespace test

def double_aux (s : Array Int) (i : Nat) : Array Int :=
  if h : i < s.size then
    let new_s := s.set! i (2 * s[i]!)
    double_aux new_s (i + 1)
  else
    s

-- 测试：函数归纳应该被自动检测和应用一次
theorem test_func_induction (s : Array Int) (i : Nat) :
    (double_aux s i).size = s.size := by
  aesop?

end test

