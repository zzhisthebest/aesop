import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def myMin_precond (x : Int) (y : Int) : Prop :=
  True

def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  if x < y then x else y

@[reducible, simp]
def myMin_postcond (x : Int) (y : Int) (result: Int) (h_precond : myMin_precond (x) (y)) :=
  (x ≤ y → result = x) ∧ (x > y → result = y)


theorem myMin_eq_left_of_lt
    (x y : Int) (hlt : x < y) (h_precond : myMin_precond x y) :
    myMin x y h_precond = x:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp