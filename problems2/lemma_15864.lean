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


theorem any_outer_eq_true (a b : Array Int) :
    a.any (fun x => b.any fun y => x = y) = true ↔
      ∃ i, i < a.size ∧ b.any (fun y => a[i]! = y):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp