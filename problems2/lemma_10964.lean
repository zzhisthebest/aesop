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


theorem any_of_mem_eq (arr : Array Int) (a : Int) (ha : a ∈ arr) :
    arr.any (fun x => x = a):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp