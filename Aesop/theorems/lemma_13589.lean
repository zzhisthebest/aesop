module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_13589
public def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = e

public def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0

public def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  linearSearchAux a e 0

public def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)


public theorem exists_forward (a : Array Int) (e : Int) {n i : Nat}
    (h₁ : i < a.size) (h₂ : a[i]! = e) (h₃ : n ≤ i) :
    ∃ j, j < a.size ∧ a[j]! = e ∧ n + 1 ≤ j:= by 
sorry


end tmp_lemma_13589