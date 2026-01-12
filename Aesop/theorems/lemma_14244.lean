module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14244
public def maxArray_precond (a : Array Int) : Prop :=
  a.size > 0

public def maxArray_aux (a : Array Int) (index : Nat) (current : Int) : Int :=
  if index < a.size then
    let new_current := if current > a[index]! then current else a[index]!
    maxArray_aux a (index + 1) new_current
  else
    current

public def maxArray (a : Array Int) (h_precond : maxArray_precond (a)) : Int :=
  maxArray_aux a 1 a[0]!

public def maxArray_postcond (a : Array Int) (result: Int) (h_precond : maxArray_precond (a)) :=
  (∀ (k : Nat), k < a.size → result >= a[k]!) ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)


public theorem if_eq (x y : Int) :
    (if x > y then x else y) = x ∨ (if x > y then x else y) = y:= by 
sorry


end tmp_lemma_14244