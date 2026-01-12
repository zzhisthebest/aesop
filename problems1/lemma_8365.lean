import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def cubeElements_precond (a : Array Int) : Prop :=
  True

def cubeElements (a : Array Int) (h_precond : cubeElements_precond (a)) : Array Int :=
  a.map (fun x => x * x * x)

@[reducible, simp]
def cubeElements_postcond (a : Array Int) (result: Array Int) (h_precond : cubeElements_precond (a)) :=
  (result.size = a.size) ∧
  (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)


theorem cubeElements_get (a : Array Int) (h_precond : cubeElements_precond a)
    (i : Nat) (hi : i < a.size) :
    (cubeElements a h_precond)[i]! = a[i]! * a[i]! * a[i]!:= by 
aesop?(config := { enableGrind := false })


end tmp