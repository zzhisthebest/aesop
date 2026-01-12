import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  True

def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  if x % 2 = 0 then true else false

@[reducible, simp]
def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  result = true ↔ ∃ k : Int, x = 2 * k


theorem dvd_imp_mod_eq_zero (h : (2 : Int) ∣ x) : x % (2 : Int) = 0:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp