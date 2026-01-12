module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_1088
public def isItEight_precond (n : Int) : Prop :=
  True

public def isItEight (n : Int) (h_precond : isItEight_precond (n)) : Bool :=
  let rec hasDigitEight (m : Nat) : Bool :=
    if m <= 0 then false
    else if m % 10 == 8 then true
    else hasDigitEight (m / 10)
    termination_by m

  let absN := Int.natAbs n
  n % 8 == 0 || hasDigitEight absN

public def isItEight_postcond (n : Int) (result: Bool) (h_precond : isItEight_precond (n)) : Prop :=
  let absN := Int.natAbs n;
  (n % 8 == 0 ∨ ∃ i, absN / (10^i) % 10 == 8) ↔ result


public theorem digit_shift (m : Nat) (i : Nat) :
    m / (10 ^ (i.succ)) % 10 = (m / 10) / (10 ^ i) % 10:= by 
sorry


end tmp_lemma_1088