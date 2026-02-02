import Codetic
set_option maxHeartbeats 0
set_option trace.codetic.zzh_custom true

namespace DynamicInductionTest

-- Test 1: 三个 List 变量 - 应该为 xs, ys, zs 各创建一个规则
theorem test_three_lists (xs ys zs : List Nat) :
    xs.length + ys.length + zs.length = zs.length + ys.length + xs.length := by
  codetic

-- Test 2: 混合 Nat 和 List 变量
theorem test_mixed (n m : Nat) (xs ys : List Nat) :
    n + m + xs.length = m + n + xs.length := by
  codetic

-- Test 3: 单个变量（确保基本功能正常）
theorem test_single_list (xs : List Nat) : xs.length = xs.length := by
  codetic

-- Test 4: 需要实际 induction 的定理
def myAppend : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

theorem myAppend_nil (xs : List Nat) : myAppend xs [] = xs := by
  codetic

-- Test 5: 两个变量都可能需要 induction
theorem myAppend_assoc (xs ys zs : List Nat) :
    myAppend (myAppend xs ys) zs = myAppend xs (myAppend ys zs) := by
  codetic?

-- Test 6: 只有 Nat 变量
def natAdd : Nat → Nat → Nat
  | 0, m => m
  | n + 1, m => natAdd n m + 1

theorem natAdd_comm (n m : Nat) : natAdd n m = natAdd m n := by
  codetic

-- Test 7: 检查是否会过滤掉 induction 引入的变量
def myLength : List Nat → Nat
  | [] => 0
  | _ :: xs => 1 + myLength xs

theorem myLength_append (xs ys : List Nat) :
    myLength (myAppend xs ys) = myLength xs + myLength ys := by
  codetic

end DynamicInductionTest
