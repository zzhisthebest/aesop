/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Codetic.Builder.Basic
import Codetic.Builder.Apply
import Codetic.Builder.Constructors
import Codetic.Builder.Induction
import Codetic.Builder.NormSimp
import Codetic.Builder.Tactic

public section

open Lean
open Lean.Meta

namespace Codetic

-- TODO In the default builders below, we should distinguish between fatal and
-- nonfatal errors. E.g. if the `tactic` builder finds a declaration that is not
-- of tactic type, this is a nonfatal error and we should continue with the next
-- builder. But if the simp builder finds an equation that cannot be interpreted
-- as a simp lemma for some reason, this is a fatal error. Continuing with the
-- next builder is more confusing than anything because the user probably
-- intended to add a simp lemma.

def RuleBuilder.default : RuleBuilder := λ input =>
  match input.phase.phase with
  | .safe =>
    constructors input <|>
    -- induction input <|>  -- 已废弃，使用动态规则
    tactic input <|>
    apply input <|>
    err "a safe" input
  | .unsafe =>
    constructors input <|>
    -- induction input <|>  -- 已废弃，使用动态规则
    tactic input <|>
    apply input <|>
    err "an unsafe" input
  | .norm =>
    constructors input <|>
    tactic input <|>
    simp input <|>
    apply input <|>
    err "a norm" input
where
  err (ruleType : String) : RuleBuilder := λ input =>
    throwError m!"codetic: Unable to interpret '{input.term}' as {ruleType} rule. Try specifying a builder."

end Codetic
