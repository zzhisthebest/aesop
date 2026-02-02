/-
Copyright (c) 2022-2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CodeticTest.RuleSets0

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

@[codetic safe (rule_sets := [test_A])]
inductive A : Prop where
| intro

@[codetic safe (rule_sets := [test_B])]
inductive B : Prop where
| intro

@[codetic safe]
inductive C : Prop where
| intro

inductive D : Prop where
| intro

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : A := by
  codetic (config := { terminal := true })

example : A := by
  codetic (rule_sets := [test_A])

example : B := by
  codetic (rule_sets := [test_A, test_B])

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : C := by
  codetic (rule_sets := [-default]) (config := { terminal := true })

example : C := by
  codetic

attribute [codetic safe (rule_sets := [test_C])] C

-- Removing the attribute removes all rules associated with C from all rule
-- sets.
attribute [-codetic] C

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : C := by
  codetic (rule_sets := [test_C]) (config := { terminal := true })

example : C := by
  codetic (add safe C)

@[codetic norm simp]
theorem ad : D ↔ A :=
  ⟨λ _ => A.intro, λ _ => D.intro⟩

example : D := by
  codetic (rule_sets := [test_A])

attribute [-codetic] ad

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : D := by
  codetic (rule_sets := [test_A]) (config := { terminal := true })

example : D := by
  codetic (add norm ad) (rule_sets := [test_A])

-- Rules can also be local.

inductive E : Prop where
  | intro

section

attribute [local codetic safe] E

example : E := by
  codetic

end

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : E := by
  codetic (config := { terminal := true })

example : E := by
  constructor

-- Rules can also be scoped.

namespace EScope

attribute [scoped codetic safe] E

example : E := by
  codetic

end EScope

/--
error: tactic 'codetic' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : E := by
  codetic (config := { terminal := true })

example : E := by
  open EScope in codetic
