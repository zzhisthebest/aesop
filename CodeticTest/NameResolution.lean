/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Codetic

set_option codetic.check.all true

-- When parsing the names of declarations for local rules, Codetic should take the
-- currently opened namespaces into account.

example : List α := by
  codetic (add safe List.nil)

namespace List

example : List α := by
  codetic (add safe List.nil)

example : List α := by
  codetic (add safe nil)

end List
