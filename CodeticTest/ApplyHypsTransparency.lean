/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

def T := Unit → Nat

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : Nat := by
  codetic (config := { applyHypsTransparency := .reducible, terminal := true })

example (h : T) : Nat := by
  codetic

@[irreducible] def U := Empty

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) : U := by
  codetic (config := { applyHypsTransparency := .reducible, terminal := true })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) : U := by
  codetic (config := { terminal := true })

example (h : Unit → Empty) : U := by
  codetic (config := { applyHypsTransparency := .all })
