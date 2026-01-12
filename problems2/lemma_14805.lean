import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def myMin_precond (a : Int) (b : Int) : Prop :=
  True

def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  if a <= b then a else b

@[reducible, simp]
def myMin_postcond (a : Int) (b : Int) (result: Int) (h_precond : myMin_precond (a) (b)) :=
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)


theorem myMin_eq_left_or_right_of_not_le (a b : Int) (h : ¬ a ≤ b) :
    myMin a b (by trivial) = a ∨ myMin a b (by trivial) = b:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp