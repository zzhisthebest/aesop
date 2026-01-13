/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Batteries.Data.List.Basic

public section

namespace List

variable {α : Type u}

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. -/
@[elab_as_elim]
def reverse_RecOn {motive : List α → Sort v} (l : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : motive l :=
  match h : reverse l with
  | [] => cast (congrArg motive (by simpa using congrArg reverse h.symm))
      nil
  | head :: tail =>
    cast (congrArg motive (by simpa using congrArg reverse h.symm))
      (append_singleton _ head (reverse_RecOn (reverse tail) nil append_singleton))
termination_by l.length
decreasing_by
  simp_wf
  rw [← length_reverse (as := l), h, length_cons]
  simp

end List
