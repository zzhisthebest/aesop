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


theorem mem_of_get! {arr : Array Int} {i : Nat}
    (hi : i < arr.size) : arr[i]! ∈ arr:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp