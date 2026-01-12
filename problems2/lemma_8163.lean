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


theorem mod_eq_sub_mul_div (n : Int) : n % 2 = n - 2 * (n / 2):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp