import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0

def hasCommonElement (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) : Bool :=
  a.any fun x => b.any fun y => x = y

@[reducible, simp]
def hasCommonElement_postcond (a : Array Int) (b : Array Int) (result: Bool) (h_precond : hasCommonElement_precond (a) (b)) :=
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result


theorem exists_eq_iff_any (arr₁ arr₂ : Array Int) :
    (∃ i j, i < arr₁.size ∧ j < arr₂.size ∧ arr₁[i]! = arr₂[j]!) ↔
      ∃ i, i < arr₁.size ∧ (arr₂.any fun y => arr₁[i]! = y) = true:= by 
  aesop?


end tmp