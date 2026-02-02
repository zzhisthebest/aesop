/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

-- Forward rules always operate at reducible transparency.

def T := Unit → Empty

variable {α : Type}

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : Unit) : α := by
  codetic (config := { terminal := true })

def U := Unit

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : U) : α := by
  codetic (config := { terminal := true })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : U) : α := by
  codetic (add forward safe h) (config := { terminal := true })

abbrev V := Unit

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) (u : V) : α := by
  codetic (config := { terminal := true })

example (h : Unit → Empty) (u : V) : α := by
  codetic (add forward safe h)
