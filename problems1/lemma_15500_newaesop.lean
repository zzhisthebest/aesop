import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def SelectionSort_precond (a : Array Int) : Prop :=
  True

def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a

def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  let indices := List.range a.size
  indices.foldl (fun arr i =>
    let minIdx := findMinIndexInRange arr i a.size
    swap arr i minIdx
  ) a

@[reducible, simp]
def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList


theorem SelectionSort_sorted (a : Array Int) (h_precond : SelectionSort_precond a) :
    List.Pairwise (· ≤ ·) (SelectionSort a h_precond).toList:= by 
  aesop?


end tmp