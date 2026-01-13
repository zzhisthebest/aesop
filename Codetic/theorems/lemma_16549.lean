module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_16549
public def Triple_precond (x : Int) : Prop :=
  True

public def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    let y := 2 * x
    x + y

public def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result


public theorem add_mul_two (x : Int) : 2 * x + 4 * x = 6 * x:= by 
sorry


end tmp_lemma_16549