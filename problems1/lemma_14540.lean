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


theorem myMin_spec_eq (x y : Int) (hpre : myMin_precond x y) (heq : x = y) :
    myMin_postcond x y (myMin x y hpre) hpre:= by 
codetic?(config := { enableGrind := false })


end tmp