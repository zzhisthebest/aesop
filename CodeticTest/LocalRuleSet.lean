/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

-- We used to add local rules to the `default` rule set, but this doesn't work
-- well when the default rule set is disabled.

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Unit := by
  codetic (rule_sets := [-default, -builtin]) (config := { terminal := true })

example : Unit := by
  codetic (add safe PUnit.unit) (rule_sets := [-default, -builtin])
