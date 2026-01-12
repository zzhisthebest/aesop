module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14200
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


public theorem step_preserves_upper (a : Array Int) (i : Nat) (cur : Int)
    (h_i : i < a.size)
    (hUB : ∀ k, k < i → a[k]! ≤ cur) :
    ∀ k, k < i+1 → a[k]! ≤ (if cur > a[i]! then cur else a[i]!):= by 
sorry


end tmp_lemma_14200