import Aesop
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


theorem max_eq_c_of_ge (a b c : Int)
    (h₁ : ¬(a ≥ b ∧ a ≥ c))
    (h₂ : ¬(b ≥ a ∧ b ≥ c)) :
    max a (max b c) = c:= by 
aesop?(config := { enableGrind := false })


end tmp