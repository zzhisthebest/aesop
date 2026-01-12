import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  True

def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  a * b

@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  result - a * b = 0 ∧ a * b - result = 0


theorem self_sub_mul (a b : Int) : a * b - (a * b) = 0:= by 
aesop?(config := { enableGrind := false })


end tmp