/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

set_option trace.codetic.proof true

/--
error: tactic 'codetic' failed, made no progress
---
trace: [codetic.proof] <no proof>
-/
#guard_msgs in
example : α := by
  codetic

@[codetic norm simp]
def F := False

set_option pp.mvars false in
/--
warning: codetic: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
---
trace: [codetic.proof] id ?_
-/
#guard_msgs in
example : F := by
  codetic
