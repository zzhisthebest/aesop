module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10000
public def swapFirstAndLast_precond (a : Array Int) : Prop :=
  a.size > 0

public def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  let first := a[0]!
  let last := a[a.size - 1]!
  a.set! 0 last |>.set! (a.size - 1) first

public def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) (h_precond: swapFirstAndLast_precond a) : Prop :=
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)


public theorem get_swap_last (a : Array Int) (first last : Int) (h₁ : a.size > 0) :
    (a.set! 0 last |>.set! (a.size - 1) first)[a.size - 1]! = first:= by 
sorry


end tmp_lemma_10000