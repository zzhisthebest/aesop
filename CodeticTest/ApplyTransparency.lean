/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

def T := True

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  codetic (add safe apply True.intro) (config := { terminal := true })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  codetic (add safe apply (transparency := default) True.intro)
    (config := { terminal := true })

example : T := by
  codetic (add safe apply (transparency! := default) True.intro)

@[irreducible] def U := T

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  codetic (add safe apply True.intro) (config := { terminal := true })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  codetic (add safe apply (transparency := default) True.intro)
    (config := { terminal := true })

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  codetic (add safe apply (transparency! := default) True.intro)
    (config := { terminal := true })

example : U := by
  codetic (add safe apply (transparency! := all) True.intro)
