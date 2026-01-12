module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_13565
public def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  True

public def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0

public def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)


public theorem if_lt_succ (n m : Nat) :
    (if h : n < Nat.succ m then n else Nat.succ m) ≤ Nat.succ m:= by 
sorry


end tmp_lemma_13565