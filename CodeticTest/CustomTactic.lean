/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

def Foo := True

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Foo := by
  codetic (config := { terminal := true })

example : Foo := by
  simp [Foo]

open Lean.Elab.Tactic in
@[codetic safe]
def myTactic : TacticM Unit := do
  evalTactic $ ← `(tactic| rw [Foo])

example : Foo := by
  set_option codetic.check.script false in
  set_option codetic.check.script.steps false in
  codetic
