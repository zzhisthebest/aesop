module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_13258
public def ComputeIsEven_precond (x : Int) : Prop :=
  True

public def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  if x % 2 = 0 then true else false

public def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  result = true ↔ ∃ k : Int, x = 2 * k


public theorem mod_two_eq_zero_iff_even (x : Int) :
    x % 2 = 0 ↔ ∃ k : Int, x = 2 * k:= by 
sorry


end tmp_lemma_13258