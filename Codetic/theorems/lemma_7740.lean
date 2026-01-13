module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_7740
public def Triple_precond (x : Int) : Prop :=
  True

public def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := x * 2
  y + x

public def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


public theorem mul_three_eq (x : Int) : x * 2 + x = x * 3:= by 
sorry


end tmp_lemma_7740