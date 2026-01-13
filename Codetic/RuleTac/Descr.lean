module

public import Codetic.RuleTac.Basic
public import Codetic.Script.CtorNames
public import Codetic.Forward.Match.Types

public section

open Lean Lean.Meta

namespace Codetic

inductive RuleTacDescr
  | apply (term : RuleTerm) (md : TransparencyMode)
  | constructors (constructorNames : Array Name) (md : TransparencyMode)
  | forward (term : RuleTerm) (immediate : UnorderedArraySet PremiseIndex)
      (isDestruct : Bool)
  | cases (target : CasesTarget) (md : TransparencyMode)
      (isRecursiveType : Bool) (ctorNames : Array CtorNames)
  -- | induction (target : CasesTarget) (md : TransparencyMode)
  --     (isRecursiveType : Bool) (ctorNames : Array CtorNames)
  | inductionOnVar (fvarId : FVarId) (declName : Name) (ctorNames : Array CtorNames) (customRecursor? : Option Name := none)
  | functionInduction (funcName : Name)
  | tacticM (decl : Name)
  | ruleTac (decl : Name)
  | tacGen (decl : Name)
  | singleRuleTac (decl : Name)
  | tacticStx (stx : Syntax)
  | preprocess
  | forwardMatches (ms : Array ForwardRuleMatch)
  deriving Inhabited

namespace RuleTacDescr

def forwardRuleMatches? : RuleTacDescr → Option (Array ForwardRuleMatch)
  | forwardMatches ms => ms
  | _ => none

end RuleTacDescr

end Codetic
