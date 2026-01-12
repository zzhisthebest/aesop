import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def cubeSurfaceArea_precond (size : Nat) : Prop :=
  True

def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  6 * size * size

@[reducible, simp]
def cubeSurfaceArea_postcond (size : Nat) (result: Nat) (h_precond : cubeSurfaceArea_precond (size)) :=
  result - 6 * size * size = 0 ∧ 6 * size * size - result = 0


theorem cubeSurfaceArea_sub_self (size : Nat)
    (h_precond : cubeSurfaceArea_precond (size)) :
    cubeSurfaceArea size h_precond - 6 * size * size = 0:= by 
aesop?(config := { enableGrind := false })


end tmp