import Aesop
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


theorem div_mul_self_three (x : Int) (h₃ : (3 : Int) ≠ 0) :
    (x * 3) / 3 = x:= by 
aesop?(config := { enableGrind := false })


end tmp