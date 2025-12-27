import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x = 0 then 0 else
    let y := 2 * x
    x + y

@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


theorem Triple_if_eq (x : Int) (h : Triple_precond x) :
    (if x = 0 then (0 : Int) else let y := 2 * x; x + y) = if x = 0 then 0 else x + 2 * x:= by 
aesop


end tmp