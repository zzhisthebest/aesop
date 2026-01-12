module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_9713
public def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  k < s.size

public def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  s.eraseIdx! k

public def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)


public theorem eraseIdx_get_right (s : Array Int) (k i : Nat) (h : k < s.size)
    (hi : i < (s.eraseIdx k h).size) (hge : i ≥ k) :
    (s.eraseIdx k h)[i]! = s[i + 1]!:= by 
sorry


end tmp_lemma_9713