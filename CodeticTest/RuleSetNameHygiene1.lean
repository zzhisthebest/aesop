/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CodeticTest.RuleSetNameHygiene0

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

macro "codetic_test" : tactic => `(tactic| codetic (rule_sets := [test]))

@[codetic safe (rule_sets := [test])]
structure TT where

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : TT := by
  codetic (config := { terminal := true })

example : TT := by
  codetic_test
