import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def elementWiseModulo_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)

def elementWiseModulo (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) : Array Int :=
  a.mapIdx (fun i x => x % b[i]!)

@[reducible, simp]
def elementWiseModulo_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :=
  result.size = a.size ∧
  (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)


theorem elementWiseModulo_get (a b : Array Int)
    (h_precond : elementWiseModulo_precond a b) (i : Nat)
    (hi : i < a.size) :
    (elementWiseModulo a b h_precond)[i]! = a[i]! % b[i]!:= by 
codetic?(config := { enableGrind := false })


end tmp