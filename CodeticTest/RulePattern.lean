/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Codetic

set_option codetic.check.all true

macro "codetic!" : tactic =>
  `(tactic| codetic (config := { warnOnNonterminal := false }))

axiom falso : ∀ {α : Sort _}, α

macro "falso" : tactic => `(tactic| exact falso)

@[codetic norm -100 forward (pattern := (↑n : Int))]
axiom nat_pos (n : Nat) : 0 ≤ (↑n : Int)

example (m n : Nat) : (↑m : Int) < 0 ∧ (↑n : Int) > 0 := by
  set_option codetic.check.script.steps false in -- TODO lean4#4315
  set_option codetic.check.script false in
  codetic (config := { enableSimp := false, warnOnNonterminal := false })
  all_goals
    guard_hyp fwd   : 0 ≤ (m : Int)
    guard_hyp fwd_1 : 0 ≤ (n : Int)
    falso

@[codetic safe forward (pattern := min x y)]
axiom foo : ∀ {x y : Nat} (_ : 0 < x) (_ : 0 < y), 0 < min x y

example (hx : 0 < x) (hy : 0 < y) (_ : min x y < z): False := by
  codetic!
  guard_hyp fwd : 0 < min x y
  falso

axiom abs (n : Int) : Nat

notation "|" t "|" => abs t

@[codetic safe forward (pattern := |a + b|)]
axiom triangle (a b : Int) : |a + b| ≤ |a| + |b|

@[codetic safe apply (pattern := (0 : Nat))]
axiom falso' : True → False

/--
error: tactic 'codetic' failed, made no progress
Initial goal:
  ⊢ False
-/
#guard_msgs in
example : False := by
  codetic

example (h : n = 0) : False := by
  codetic (rule_sets := [-builtin])

-- Patterns may only contain variables mentioned in the rule.

/-- error: Unknown identifier `z` -/
#guard_msgs in
@[codetic safe forward (pattern := z)]
axiom quuz (x y : Nat) : True

-- When a premise of a forward rule is mentioned in a pattern, it can't also
-- be an immediate argument.

@[codetic safe forward (pattern := (↑x : Int)) (immediate := [y])]
axiom bar (x y : Nat) : True

/--
error: codetic: forward builder: argument 'x' cannot be immediate since it is already determined by a pattern
-/
#guard_msgs in
@[codetic safe forward (pattern := (↑x : Int)) (immediate := [y, x])]
axiom baz (x y : Nat) : True

-- For types with 'reducibly hidden' forall binders, the pattern can only refer
-- to the syntactically visible variables.

abbrev T := (tt : True) → False

/-- error: Unknown identifier `tt` -/
#guard_msgs in
@[codetic safe forward (pattern := tt)]
axiom falso₁ : T

-- We support dependencies in patterns. E.g. in the following pattern, only the
-- premise `x` occurs syntactically, but the type of `x` depends on `a` and `p`,
-- so these premises are also determined by the pattern substitution.
-- (Thanks to Son Ho for this test case.)

@[codetic safe forward (pattern := x)]
theorem get_prop {a : Type} {p : a → Prop} (x : Subtype p) : p x.val :=
  x.property

example {a : Type} {p : a → Prop} (x : Subtype p × Subtype p)
    (h : x.1.val = x.2.val) : p x.1.val ∧ p x.2.val := by
  saturate
  apply And.intro <;> assumption
