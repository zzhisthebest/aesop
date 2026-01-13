module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10868
public def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  k ≥ 1 ∧ k ≤ arr.size

public def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  arr[k - 1]!

public def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)


public theorem any_eq_true_of_mem (arr : Array Int) (a : Int) (hmem : a ∈ arr) :
    arr.any (fun x => x = a) = true:= by 
sorry


end tmp_lemma_10868