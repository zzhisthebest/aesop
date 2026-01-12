module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10107
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


public theorem even_mem_result (arr : Array Int) :
    ∀ x, x ∈ arr.toList → isEven x → x ∈
        (arr.foldl (fun (acc : Array Int) y => if isEven y then acc.push y else acc) #[]):= by 
sorry


end tmp_lemma_10107