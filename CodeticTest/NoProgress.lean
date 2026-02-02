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
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example : T := by
  codetic

@[codetic norm simp]
def F := False

/--
warning: codetic: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : F := by
  codetic

def F' := False

@[codetic safe apply]
theorem F'_def : False → F' := id

/--
warning: codetic: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : F' := by
  codetic

attribute [-codetic] F'_def
attribute [codetic 100%] F'_def

-- When an unsafe rule is applied, we don't count this as progress because the
-- remaining goal that the user gets to see is exactly the same as the initial
-- goal.

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example : F' := by
  codetic
