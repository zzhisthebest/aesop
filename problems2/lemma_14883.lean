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


theorem not_le_imp_le_of_int {a b : Int} (h : ¬ a ≤ b) : b ≤ a:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp