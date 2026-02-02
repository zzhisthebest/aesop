/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true

/--
warning: Apply builder was used for a theorem with conclusion A ↔ B.
You probably want to use the simp builder or create an alias that applies the theorem in one direction.
Use `set_option codetic.warn.applyIff false` to disable this warning.
-/
#guard_msgs in
@[codetic safe apply]
axiom foo : True ↔ True

@[codetic simp]
axiom bar : True ↔ True

set_option codetic.warn.applyIff false in
@[codetic 1% apply]
axiom baz : True ↔ True
