/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

structure Foo where
  foo ::

/--
error: tactic 'codetic' failed, made no progress
-/
#guard_msgs in
example : Foo := by
  codetic

example : Foo := by
  codetic (add safe forward Foo.foo)
