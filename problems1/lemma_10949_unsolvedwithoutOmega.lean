import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  k ≥ 1 ∧ k ≤ arr.size

def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  arr[k - 1]!

@[reducible, simp]
def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)


theorem idx_lt_size {arr k} (h : kthElement_precond arr k) :
    k - 1 < arr.size:= by 
codetic?(config := { enableGrind := false })


end tmp