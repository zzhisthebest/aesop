module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11768
public def Abs_precond (x : Int) : Prop :=
  True

public def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else x

public def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)


public theorem post_right_of_lt {x result : Int}
    (hx : x < 0) (h_eq : result = -x) :
    (x < 0 → x + result = 0):= by 
sorry


end tmp_lemma_11768