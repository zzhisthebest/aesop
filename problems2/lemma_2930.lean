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


theorem not_and_imp_lt' (a b c : Int) :
    ¬ (b ≥ a ∧ b ≥ c) → (b < a ∨ b < c):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp