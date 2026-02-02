/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true

-- From an equation where both sides contain only constructor applications
-- and variables, Codetic should derive equations about the variables.

example (h : Nat.zero = Nat.succ n) : False := by
  codetic

example (h : Nat.succ (Nat.succ n) = Nat.succ Nat.zero) : False := by
  codetic

example (h : (Nat.succ m, Nat.succ n) = (Nat.succ a, Nat.succ b)) :
    m = a ∧ n = b := by
  codetic

structure MyProd (A B : Type _) where
  toProd : A × B

example (h : MyProd.mk (x, y) = .mk (a, b)) : x = a ∧ y = b := by
  codetic
