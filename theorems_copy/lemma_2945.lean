module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_2945
public def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True

public def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c

public def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)


public theorem result_is_c (a b c : Int)
    (h₁ : ¬(a ≥ b ∧ a ≥ c)) (h₂ : ¬(b ≥ a ∧ b ≥ c)) :
    (c ≥ a ∧ c ≥ b ∧ c ≥ c) ∧ (c = a ∨ c = b ∨ c = c):= by 
sorry


end tmp_lemma_2945