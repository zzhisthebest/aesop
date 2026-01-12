module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_8700
public def findSmallest_precond (s : Array Nat) : Prop :=
  True

public def findSmallest (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  s.toList.min?

public def findSmallest_postcond (s : Array Nat) (result: Option Nat) (h_precond : findSmallest_precond (s)) :=
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)


public theorem minOption_le_of_mem {l : List Nat} {a x : Nat}
    (h : l.min? = some a) (hx : x ∈ l) : a ≤ x:= by 
sorry


end tmp_lemma_8700