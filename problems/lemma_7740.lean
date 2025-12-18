import Aesop
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


theorem mul_ediv_cancel_right (a b : Int) (hb : b ≠ 0) :
    (a * b) / b = a:= by 
  aesop?
  aesop?(config := { useDefaultSimpSet := false })


end tmp