import Codetic
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


theorem Triple_eq_three_mul_of_lt (x : Int) (hpre : Triple_precond x) (hx : x < 18) :
    Triple x hpre = 3 * x:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp