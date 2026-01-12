import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  True

def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else x

@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)


theorem postcond_of_nonneg (x : Int) (hpre : Abs_precond x) (hge : x ≥ 0) :
    Abs_postcond x (Abs x hpre) hpre:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp