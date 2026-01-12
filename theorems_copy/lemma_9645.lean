module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_9645
public def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  k < s.size

public def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  s.eraseIdx! k

public def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)


public theorem eraseIdx!_get_ge (s : Array Int) (k i : Nat) (h_k : k < s.size)
    (h_i : i < (s.eraseIdx! k).size) (h_ge : k ≤ i) :
    (s.eraseIdx! k)[i]! = s[i + 1]!:= by 
sorry


end tmp_lemma_9645