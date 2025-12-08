/-
测试 zzh_custom trace 是否工作
-/
import Aesop

set_option trace.aesop.zzh_custom true

namespace Test

-- 定义一个简单的函数用于测试 unfold

def myAdd (a b : Nat) : Nat := a + b

-- 测试 1: 显式使用 unfold builder（应该会打印 trace）
example : myAdd 1 2 = 3 := by
  aesop (add norm unfold myAdd)
  -- 应该会看到：
  -- unfold builder: elab decl = myAdd
  -- checkUnfoldableConst: checking decl = myAdd
  -- ...

-- 测试 2: 不使用 unfold（不会打印 trace）
example : True := by
  aesop
  -- 不会打印 trace，因为没有触发 Unfold builder

end Test
