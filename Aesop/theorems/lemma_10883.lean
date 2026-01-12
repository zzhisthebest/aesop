module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10883
public def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  k ≥ 1 ∧ k ≤ arr.size

public def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  arr[k - 1]!

public def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)


public theorem any_of_kth (arr : Array Int) (k : Nat)
    (h : kthElement_precond arr k) :
    arr.any (fun x => x = arr[k - 1]! ∧ x = arr[k - 1]!):= by 
sorry


end tmp_lemma_10883