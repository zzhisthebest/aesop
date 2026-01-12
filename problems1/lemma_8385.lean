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


theorem map_size (f : Int → Int) (a : Array Int) :
    (a.map f).size = a.size:= by 
aesop?(config := { enableGrind := false })


end tmp