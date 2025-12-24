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


theorem BinarySearch_all_conj (a : Array Int) (key : Int)
    (h_precond : BinarySearch_precond a key) :
    let r := BinarySearch a key h_precond
    ((a.take r).all (fun x => x < key)) ∧
    ((a.drop r).all (fun x => x ≥ key)):= by 
  aesop?


end tmp