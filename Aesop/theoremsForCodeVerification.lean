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

attribute [simp]
Array.eraseIdx!
Int.mul_neg_of_neg_of_pos
Int.mul_comm
Array.all_iff_forall

-- attribute [aesop safe constructors cases] Array


end Aesop.TheoremsForCodeVerification
