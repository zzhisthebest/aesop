/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

/-
Regression test for a bug involving the stats extension and async elaboration.
The commands below should not panic and should show non-zero stats.
-/

set_option codetic.collectStats true
set_option trace.codetic.stats true

#guard_msgs (drop trace) in
theorem mem_spec {o : Option α} : a ∈ o ↔ o = some a := by
  codetic (add norm simp Membership.mem)

#guard_msgs (drop info) in
#codetic_stats
