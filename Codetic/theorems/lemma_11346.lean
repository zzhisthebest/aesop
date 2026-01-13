module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11346
public def isOdd (n : Int) : Bool :=
  n % 2 == 1

public def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  True

public def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  let indexedArray := a.mapIdx fun i x => (i, x)

  indexedArray.all fun (i, x) => !(isOdd i) || isOdd x

public def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))


public theorem not_or_eq_imp (p q : Bool) : (!p) || q = (p → q):= by 
sorry


end tmp_lemma_11346