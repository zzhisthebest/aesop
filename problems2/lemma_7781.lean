import Codetic
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


theorem postcond_right (x : Int) (h : Triple_precond x) :
    (Triple x h) / 3 * 3 = Triple x h:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp