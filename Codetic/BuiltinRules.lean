/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- The Codetic.BuiltinRules.* imports are needed to ensure that the tactics from
-- these files are registered.
module

public import Codetic.BuiltinRules.ApplyQuestion
public import Codetic.BuiltinRules.Assumption
public import Codetic.BuiltinRules.ApplyHyps
public import Codetic.BuiltinRules.DestructProducts
public import Codetic.BuiltinRules.Ext
public import Codetic.BuiltinRules.Grind
public import Codetic.BuiltinRules.Intros
public import Codetic.BuiltinRules.Omega
public import Codetic.BuiltinRules.Rfl
public import Codetic.BuiltinRules.Split
public import Codetic.BuiltinRules.Subst
import Codetic.Frontend.Attribute

public section

namespace Codetic.BuiltinRules

attribute [codetic (rule_sets := [codetic_builtin]) safe 0 apply] PUnit.unit

-- Hypotheses of product type are split by a separate builtin rule because the
-- `cases` builder currently cannot be used for norm rules.
attribute [codetic (rule_sets := [codetic_builtin]) safe 101 constructors]
  And Prod PProd MProd

attribute [codetic (rule_sets := [codetic_builtin]) unsafe 30% constructors]
  Exists Subtype Sigma PSigma

-- Sums are split and introduced lazily.
attribute [codetic (rule_sets := [codetic_builtin]) [safe 100 cases, 50% constructors]]
  Or Sum PSum

-- A goal ⊢ P ↔ Q is split into ⊢ P → Q and ⊢ Q → P. Hypotheses of type `P ↔ Q`
-- are treated as equations `P = Q` by the simplifier and by our builtin subst
-- rule.
attribute [codetic (rule_sets := [codetic_builtin]) safe 100 constructors] Iff

-- A negated goal Γ ⊢ ¬ P is transformed into Γ, P ⊢ ⊥. A goal with a
-- negated hypothesis Γ, h : ¬ P ⊢ Q is transformed into Γ[P := ⊥] ⊢ Q[P := ⊥]
-- by the simplifier. Quantified negated hypotheses h : ∀ x : T, ¬ P x are also
-- supported by the simplifier if the premises x can be discharged.
@[codetic (rule_sets := [codetic_builtin]) safe 0]
theorem not_intro (h : P → False) : ¬ P := h

@[codetic (rule_sets := [codetic_builtin]) norm destruct]
theorem empty_false (h : Empty) : False := nomatch h

@[codetic (rule_sets := [codetic_builtin]) norm destruct]
theorem pEmpty_false (h : PEmpty) : False := nomatch h

attribute [codetic (rule_sets := [codetic_builtin]) norm constructors] ULift

attribute [codetic (rule_sets := [codetic_builtin]) norm 0 destruct] ULift.down

@[codetic (rule_sets := [codetic_builtin]) norm simp]
theorem heq_iff_eq (x y : α) : x ≍ y ↔ x = y :=
  ⟨eq_of_heq, heq_of_eq⟩

end Codetic.BuiltinRules
