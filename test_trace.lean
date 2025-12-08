/-
在用户代码中启用 zzh_custom trace 的示例
-/
import Aesop

-- 方法 1: 在文件开头启用（对整个文件生效）
set_option trace.aesop.zzh_custom true

namespace Test

-- 现在使用 aesop 时，如果触发了 Unfold builder，就会打印 trace
example : True := by
  aesop

-- 方法 2: 在特定代码块中启用（只对局部生效）
example : True := by
  set_option trace.aesop.zzh_custom true
  aesop

-- 方法 3: 关闭 trace（如果之前开启了）
set_option trace.aesop.zzh_custom false

example : True := by
  aesop  -- 这里不会打印 trace

-- 方法 4: 在命令行中启用（不需要在代码中写）
-- lean --trace.aesop.zzh_custom=true test_trace.lean

end Test
