module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14498
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


public theorem loop_step_left
    (a : Array Int) (i : Nat) (c newC : Int)
    (hi : i < a.size)
    (hnew : newC = c)
    (hprop : ∀ j, j < i → a[j]! ≥ c) :
    (∀ j, j < i + 1 → a[j]! ≥ newC):= by 
sorry


end tmp_lemma_14498