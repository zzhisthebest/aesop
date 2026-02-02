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


theorem div_mul_eq_of_mod_zero (a b : Int) (hb₀ : b ≠ 0) (hmod : a % b = 0) :
    a / b * b = a:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp