import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  True

def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  let more := x + y
  let less := x - y
  (more, less)

@[reducible, simp]
def MultipleReturns_postcond (x : Int) (y : Int) (result: (Int × Int)) (h_precond : MultipleReturns_precond (x) (y)) :=
  result.1 = x + y ∧ result.2 + y = x


theorem let_less_eq (x y : Int) : (let less := x - y; less) = x - y:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp