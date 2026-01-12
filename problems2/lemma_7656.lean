import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x = 0 then 0 else
    let y := 2 * x
    x + y

@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


theorem spec_nonzero {x : Int} (hx : x ≠ 0) (h : Triple_precond x) :
    Triple_postcond x (Triple x h) h:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp