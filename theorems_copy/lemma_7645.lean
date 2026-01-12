module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_7645
public def Triple_precond (x : Int) : Prop :=
  True

public def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x = 0 then 0 else
    let y := 2 * x
    x + y

public def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


public theorem three_mul_eq (x : Int) : (3 : Int) * x = x + 2 * x:= by 
sorry


end tmp_lemma_7645