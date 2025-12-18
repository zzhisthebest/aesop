/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

import Aesop.Frontend.Attribute

/-!
# Theorems for Code Verification

This file contains simp theorems specifically for code verification tasks.
These theorems are tagged with `@[aesop norm simp]` so they are only used
when `aesop` is called, not by regular `simp`.

## Usage

Import this file and call:
```lean
aesop (options := { useDefaultSimpSet := false })
```

This will use:
- Only the theorems tagged here with `@[aesop norm simp]`
- Local non-recursive definitions (automatically added)
- No default `@[simp]` theorems from Lean/Mathlib
-/

namespace Aesop.TheoremsForCodeVerification


-- -- 基本算术
-- attribute [aesop norm simp] Nat.add_zero


-- -- 示例：自定义一个 simp 定理
-- @[aesop norm simp]
-- theorem nat_sub_self (n : Nat) : n - n = 0 := Nat.sub_self n

-- -- 示例：List 相关的辅助定理
-- @[aesop norm simp]
-- theorem list_count_nil (x : α) [DecidableEq α] : List.count x [] = 0 := rfl


end Aesop.TheoremsForCodeVerification
