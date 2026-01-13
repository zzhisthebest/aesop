module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_8007
public def UpdateElements_precond (a : Array Int) : Prop :=
  a.size ≥ 8

public def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2

public def UpdateElements_postcond (a : Array Int) (result: Array Int) (h_precond : UpdateElements_precond (a)) :=
  result[4]! = (a[4]!) + 3 ∧
  result[7]! = 516 ∧
  (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)


public theorem get_set_four (a : Array Int) (h : UpdateElements_precond a) :
    (a.set! 4 ((a[4]!) + 3))[4]! = (a[4]!) + 3:= by 
sorry


end tmp_lemma_8007