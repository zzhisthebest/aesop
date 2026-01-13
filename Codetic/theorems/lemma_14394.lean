module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14394
public def minArray_precond (a : Array Int) : Prop :=
  a.size > 0

public def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin

public def minArray (a : Array Int) (h_precond : minArray_precond (a)) : Int :=
  loop a 1 (a[0]!)

public def minArray_postcond (a : Array Int) (result: Int) (h_precond : minArray_precond (a)) :=
  (∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)


public theorem if_le_else (c t e : Int) (h : c ≤ e) :
    (if c > t then t else e) ≤ e:= by 
sorry


end tmp_lemma_14394