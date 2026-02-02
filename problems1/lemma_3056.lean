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


theorem not_a_not_b_implies_c_ge
    {a b c : Int}
    (hna : ¬ (a ≥ b && a ≥ c))
    (hnb : ¬ (b ≥ a && b ≥ c)) :
    c ≥ a ∧ c ≥ b:= by 
codetic?(config := { enableGrind := false })


end tmp