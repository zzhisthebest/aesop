import Codetic
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


theorem map_elem_eq (a : Array Int) (i : Nat) (h : i < a.size) :
    (a.map (fun x => x * x * x))[i]! = a[i]! * a[i]! * a[i]!:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp