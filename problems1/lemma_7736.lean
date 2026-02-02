import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := x * 2
  y + x

@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


theorem three_mul_div_three_mul_three (x : Int) :
    ((3 * x) / 3) * 3 = 3 * x:= by 
codetic?(config := { enableGrind := false })


end tmp