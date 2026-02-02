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


theorem mul_div_cancel_right_mul (a b : Int) (hb : b ≠ 0) :
    ((a * b) / b) * b = a * b:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp