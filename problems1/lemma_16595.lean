import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    let y := 2 * x
    x + y

@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


theorem mul_ediv_cancel_left_comm (a b : Int) (hb : b ≠ 0) :
    (a * b) / b = a:= by 
aesop


end tmp