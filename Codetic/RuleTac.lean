/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Codetic.RuleTac.Apply
public import Codetic.RuleTac.Basic
public import Codetic.RuleTac.Cases
public import Codetic.RuleTac.Forward
public import Codetic.RuleTac.Induction
public import Codetic.RuleTac.Preprocess
public import Codetic.RuleTac.Tactic
public import Codetic.RuleTac.Descr

public section

open Lean

namespace Codetic.RuleTacDescr

protected def run : RuleTacDescr → RuleTac
  | apply t md => RuleTac.apply t md
  | constructors cs md => RuleTac.applyConsts cs md
  | forward t immediate clear => RuleTac.forward t immediate clear
  | cases target md isRecursiveType ctorNames =>
    RuleTac.cases target md isRecursiveType ctorNames
  -- | induction target md isRecursiveType ctorNames =>
  --   RuleTac.induction target md isRecursiveType ctorNames
  | inductionOnVar fvarId declName ctorNames customRecursor? =>
    RuleTac.Induction.inductionOnSpecificVar fvarId declName ctorNames customRecursor?
  | functionInduction funcName =>
    RuleTac.Induction.functionInductionRule funcName
  | tacticM decl => RuleTac.tacticM decl
  | singleRuleTac decl => RuleTac.singleRuleTac decl
  | ruleTac decl => RuleTac.ruleTac decl
  | tacticStx stx => RuleTac.tacticStx stx
  | tacGen decl => RuleTac.tacGen decl
  | preprocess => RuleTac.preprocess
  | forwardMatches m => RuleTac.forwardMatches m

end RuleTacDescr
