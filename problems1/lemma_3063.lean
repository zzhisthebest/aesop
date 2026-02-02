import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True

def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c

@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)


theorem maxOfThree_spec_a (a b c : Int) (h_precond : maxOfThree_precond a b c)
    (h : a ≥ b && a ≥ c) :
    maxOfThree_postcond a b c (maxOfThree a b c h_precond) h_precond:= by 
codetic?(config := { enableGrind := false })


end tmp