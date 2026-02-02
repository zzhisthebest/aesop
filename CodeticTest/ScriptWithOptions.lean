/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true

/--
info: Try this:

  [apply]   simp_all (config := { }) only
-/
#guard_msgs in
example : True := by
  codetic? (config := {}) (simp_config := {})
