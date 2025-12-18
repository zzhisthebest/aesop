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

attribute [aesop simp]
Array.any_eq_true
Array.size_eq_zero_iff
List.all_map
List.head?_filter
List.filter_eq_self
List.find?_isSome
List.Pairwise.nil
List.length_zipIdx
String.append_empty
String.toList
String.data_eq_nil_iff
String.length_empty
not_exists
Nat.not_lt
ne_eq
String.mk_eq_asString
List.asString_eq_empty_iff
List.data_asString
not_false_eq_true
Int.mul_ediv_cancel_left
List.pairwise_cons
List.mem_flatMap
List.mem_map
List.asString_append
List.length_eq_zero_iff
List.length_mergeSort
decide_eq_false_iff_not
Nat.div_eq_zero_iff
List.mem_cons

-- -- 示例：自定义一个 simp 定理
-- @[aesop norm simp]
-- theorem nat_sub_self (n : Nat) : n - n = 0 := Nat.sub_self n

-- -- 示例：List 相关的辅助定理
-- @[aesop norm simp]
-- theorem list_count_nil (x : α) [DecidableEq α] : List.count x [] = 0 := rfl


end Aesop.TheoremsForCodeVerification
