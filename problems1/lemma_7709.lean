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


theorem triple_eq_three_mul (x : Int) (h_precond : Triple_precond x) :
    Triple x h_precond = 3 * x:= by 
aesop


end tmp