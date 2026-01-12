module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14510
public def myMin_precond (x : Int) (y : Int) : Prop :=
  True

public def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  if x < y then x else y

public def myMin_postcond (x : Int) (y : Int) (result: Int) (h_precond : myMin_precond (x) (y)) :=
  (x ≤ y → result = x) ∧ (x > y → result = y)


public theorem le_and_not_lt_imp_eq (x y : Int) (hle : x ≤ y) (hnotlt : ¬ x < y) : x = y:= by 
sorry


end tmp_lemma_14510