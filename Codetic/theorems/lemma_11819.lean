module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11819
public def Abs_precond (x : Int) : Prop :=
  True

public def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else x

public def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)


public theorem if_neg_of_ge (x : Int) (h : 0 ≤ x) :
    (if x < 0 then (-x) else x) = x:= by 
sorry


end tmp_lemma_11819