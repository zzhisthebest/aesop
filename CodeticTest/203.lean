/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic.Frontend

-- Thank to Damiano Testa for this bug report.

/--
info: @[codetic (rule_sets := [builtin✝]) safe✝ apply✝]
example : True✝ :=
  trivial✝
-/
#guard_msgs in
#eval do
  let stx ← `(@[codetic (rule_sets := [builtin]) safe apply] example : True := trivial)
  Lean.logInfo stx
