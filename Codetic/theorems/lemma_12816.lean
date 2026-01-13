module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12816
public def isEven (n : Int) : Bool :=
  n % 2 = 0

public def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  True

public def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < arr.size then
      if isEven (arr.getD i 0) then
        loop (i + 1) (acc.push (arr.getD i 0))
      else
        loop (i + 1) acc
    else
      acc
  loop 0 (Array.mkEmpty 0)

public def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :=
  result.all (fun x => isEven x && x ∈ arr) ∧
  List.Pairwise (fun (x, i) (y, j) => if i < j then arr.idxOf x ≤ arr.idxOf y else true) (result.toList.zipIdx)


public theorem pairwise_push_of_mem (arr : Array Int) (x : Int)
    (hx : x ∈ arr) (hidx : arr.idxOf x = arr.size) :
    List.Pairwise
      (fun (y, i) (z, j) =>
        if i < j then arr.idxOf y ≤ arr.idxOf z else true)
      (arr.toList.zipIdx) →
    List.Pairwise
      (fun (y, i) (z, j) =>
        if i < j then arr.idxOf y ≤ arr.idxOf z else true)
      ((arr.push x).toList.zipIdx):= by 
sorry


end tmp_lemma_12816