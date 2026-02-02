/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true

example : True := by
  codetic

example : Unit := by
  codetic

example : PUnit.{u} := by
  codetic

example (h : False) : α := by
  codetic

example (h : Empty) : α := by
  codetic

example (h : PEmpty.{u}) : α := by
  codetic
