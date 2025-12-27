import Aesop
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


theorem mul_ediv_eq_sub_mod (x y : Int) : y * (x / y) = x - x % y:= by 
aesop


end tmp