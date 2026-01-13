/-
Copyright (c) 2021-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module


public section

open Lean

namespace Codetic

abbrev RuleSetName := Name -- Not really an abbreviation is it?

def defaultRuleSetName : RuleSetName := `codetic_default

def builtinRuleSetName : RuleSetName := `codetic_builtin

def localRuleSetName : RuleSetName := `codetic_local

def builtinRuleSetNames : Array RuleSetName :=
  #[defaultRuleSetName, builtinRuleSetName]

def RuleSetName.isReserved (n : RuleSetName) : Bool :=
  n == localRuleSetName || builtinRuleSetNames.contains n

end Codetic
