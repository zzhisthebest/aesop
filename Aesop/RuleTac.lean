/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.RuleTac.Apply
public import Aesop.RuleTac.Basic
public import Aesop.RuleTac.Cases
public import Aesop.RuleTac.Forward
public import Aesop.RuleTac.Induction
public import Aesop.RuleTac.Preprocess
public import Aesop.RuleTac.Tactic
public import Aesop.RuleTac.Descr

public section

open Lean

namespace Aesop.RuleTacDescr

protected def run : RuleTacDescr → RuleTac
  | apply t md => RuleTac.apply t md
  | constructors cs md => RuleTac.applyConsts cs md
  | forward t immediate clear => RuleTac.forward t immediate clear
  | cases target md isRecursiveType ctorNames =>
    RuleTac.cases target md isRecursiveType ctorNames
  -- | induction target md isRecursiveType ctorNames =>
  --   RuleTac.induction target md isRecursiveType ctorNames
  | inductionOnVar fvarId declName ctorNames =>
    RuleTac.Induction.inductionOnSpecificVar fvarId declName ctorNames
  | functionInduction funcName numFixedVars numInductVars =>
    RuleTac.Induction.functionInductionRule funcName numFixedVars numInductVars
  | tacticM decl => RuleTac.tacticM decl
  | singleRuleTac decl => RuleTac.singleRuleTac decl
  | ruleTac decl => RuleTac.ruleTac decl
  | tacticStx stx => RuleTac.tacticStx stx
  | tacGen decl => RuleTac.tacGen decl
  | preprocess => RuleTac.preprocess
  | forwardMatches m => RuleTac.forwardMatches m

end RuleTacDescr
