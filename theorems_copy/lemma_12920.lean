module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12920
public def isDigit (c : Char) : Bool :=
  (c ≥ '0') && (c ≤ '9')

public def allDigits_precond (s : String) : Prop :=
  True

public def allDigits (s : String) (h_precond : allDigits_precond (s)) : Bool :=
  let rec loop (it : String.Iterator) : Bool :=
    if it.atEnd then
      true
    else
      if !isDigit it.curr then
        false
      else
        loop it.next
  loop s.iter

public def allDigits_postcond (s : String) (result: Bool) (h_precond : allDigits_precond (s)) :=
  (result = true ↔ ∀ c ∈ s.toList, isDigit c)


public theorem String.all_eq_true (s : String) (p : Char → Bool) :
    s.all p = true ↔ ∀ c ∈ s.toList, p c:= by 
sorry


end tmp_lemma_12920