/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Codetic

set_option codetic.check.all true

@[codetic 50% cases]
inductive FancyAnd (α β : Prop) : Prop
  | dummy (p : Empty)
  | and (a : α) (b : β)

attribute [codetic safe -51 cases] Empty

example {α β} (h : FancyAnd α β) : α ∧ β := by
  codetic

@[codetic safe cases (cases_patterns := [All _ [], All _ (_ :: _)])]
inductive All (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons : P x → All P xs → All P (x :: xs)

@[codetic 99% constructors]
structure MyTrue : Prop

-- Without the patterns on the `cases` rule for `All`, this test would loop
-- since the `constructors` rule would never be applied.
example {P : α → Prop} (h : All P (x :: xs)) : MyTrue := by
  codetic
