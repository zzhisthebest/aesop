module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_15534
public def SelectionSort_precond (a : Array Int) : Prop :=
  True

public def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

public def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a

public def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  let indices := List.range a.size
  indices.foldl (fun arr i =>
    let minIdx := findMinIndexInRange arr i a.size
    swap arr i minIdx
  ) a

public def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList


public theorem arraySwap_isPerm (a : Array Int) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (hij : i ≠ j) :
    List.isPerm a.toList (a.swap i j).toList:= by 
sorry


end tmp_lemma_15534