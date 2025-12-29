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


theorem get_map_eq (a : Array Int) (f : Int → Int) (i : Nat) (h : i < a.size) :
    (a.map f)[i]! = f (a[i]!):= by 
aesop


end tmp