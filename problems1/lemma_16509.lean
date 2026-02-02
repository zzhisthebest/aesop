import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  x * 3

@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


theorem mul_div_cancel_left_mul (x : Int) :
    ((x * 3) / 3) * 3 = x * 3:= by 
codetic?(config := { enableGrind := false })


end tmp