module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10242
public def isEven (n : Int) : Bool :=
  n % 2 = 0

public def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True

public def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]

public def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)


public theorem order_findEvenNumbers_aux (l : List Int) {x y : Int}
    (hx : x ∈ l) (hy : y ∈ l) (hxe : isEven x) (hye : isEven y) :
    l.idxOf x ≤ l.idxOf y →
    (l.foldl (fun (acc : Array Int) z =>
          if isEven z then acc.push z else acc) #[]).toList.idxOf x ≤
    (l.foldl (fun (acc : Array Int) z =>
          if isEven z then acc.push z else acc) #[]).toList.idxOf y:= by 
sorry


end tmp_lemma_10242