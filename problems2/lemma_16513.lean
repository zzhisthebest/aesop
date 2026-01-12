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


theorem cancel_then_mul (x c : Int) (hc : c ≠ 0) :
    ((x * c) / c) * c = x * c:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp