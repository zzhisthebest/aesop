/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true
set_option codetic.smallErrorMessages true

-- Basic examples

structure TT₁ where

/-- error: tactic 'codetic' failed, made no progress -/
#guard_msgs in
example : TT₁ := by
  codetic

add_codetic_rules safe TT₁

example : TT₁ := by
  codetic

-- Local rules

structure TT₂ where

namespace Test

local add_codetic_rules safe TT₂

example : TT₂ := by
  codetic

end Test

/-- error: tactic 'codetic' failed, made no progress -/
#guard_msgs in
example : TT₂ := by
  codetic

-- Scoped rules

structure TT₃ where

namespace Test

scoped add_codetic_rules safe TT₃

example : TT₃ := by
  codetic

end Test

/-- error: tactic 'codetic' failed, made no progress -/
#guard_msgs in
example : TT₃ := by
  codetic

def Test.example : TT₃ := by
  codetic

-- Tactics

structure TT₄ where

/-- error: tactic 'codetic' failed, made no progress -/
#guard_msgs in
example : TT₄ := by
  codetic

add_codetic_rules safe (by exact TT₄.mk)

example : TT₄ := by
  codetic

-- Multiple rules

axiom T : Type
axiom U : Type
axiom f : T → U
axiom t : T

/-- error: tactic 'codetic' failed, made no progress -/
#guard_msgs in
example : U := by
  codetic

add_codetic_rules safe [(by apply f), t]

noncomputable example : U := by
  codetic
