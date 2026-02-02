/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CodeticTest.DefaultRuleSetsInit

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

@[codetic norm unfold (rule_sets := [regular₁])]
def T := True

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  codetic (config := { terminal := true })

example : T := by
  codetic (rule_sets := [regular₁])

@[codetic norm unfold (rule_sets := [regular₂, dflt₁])]
def U := True

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  codetic (rule_sets := [-dflt₁]) (config := { terminal := true })

example : U := by
  codetic
