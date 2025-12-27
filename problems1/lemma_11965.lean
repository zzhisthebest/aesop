import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  List.Pairwise (· ≤ ·) a.toList

def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo

def BinarySearch (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) : Nat :=
  binarySearchLoop a key 0 a.size

@[reducible, simp]
def BinarySearch_postcond (a : Array Int) (key : Int) (result: Nat) (h_precond : BinarySearch_precond (a) (key)) :=
  result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))


theorem upper_bound_inv (a : Array Int) (key : Nat) (lo hi : Nat) :
  (∀ i, hi ≤ i → i < a.size → a[i]! ≥ key) → (a.drop hi).all (fun x => x ≥ key):= by 
aesop


end tmp