module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12680
public def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True

public def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c

public def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)


public theorem le_total_three (a b c : Int) :
    (a ≤ b ∧ a ≤ c) ∨ (b ≤ a ∧ b ≤ c) ∨ (c ≤ a ∧ c ≤ b):= by 
sorry


end tmp_lemma_12680