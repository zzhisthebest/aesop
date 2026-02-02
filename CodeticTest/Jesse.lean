/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Vogel, Jannis Limperg
-/

import Codetic

set_option codetic.check.all true

axiom Ring : Type
axiom Morphism (R S : Ring) : Type

@[codetic 99%]
axiom ZZ : Ring

@[codetic 99%]
axiom f : Morphism ZZ ZZ

noncomputable example : Σ (R : Ring), Morphism R R := by
  codetic

axiom domain (R : Ring) : Prop

@[codetic 99%]
axiom ZZ_domain : domain ZZ

noncomputable example : ∃ (R : Ring), domain R := by
  codetic
