/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Lean.Elab.Exception

public section

open Lean Lean.Elab

namespace Codetic.Frontend.Parser

declare_syntax_cat Codetic.bool_lit (behavior := symbol)

syntax "true" : Codetic.bool_lit
syntax "false" : Codetic.bool_lit

end Parser

def elabBoolLit [Monad m] [MonadRef m] [MonadExceptOf Exception m]
    (stx : TSyntax `Codetic.bool_lit) : m Bool :=
  withRef stx do
    match stx with
    | `(bool_lit| true) => return true
    | `(bool_lit| false) => return false
    | _ => throwUnsupportedSyntax

end Codetic.Frontend
