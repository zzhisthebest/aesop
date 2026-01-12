import Aesop
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


theorem any_of_eq_at_index (arr : Array Int) (i : Nat) (h : i < arr.size) :
    arr.any (fun x => x = arr[i]! ∧ x = arr[i]!) = true:= by 
aesop?(config := { enableGrind := false })


end tmp