import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  True

def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  (a + b) / 2

@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  2 * result = a + b - ((a + b) % 2)


theorem ediv_add_emod_eq (x y : Int) : x = y * (x / y) + x % y:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp