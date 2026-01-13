module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11403
public def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

public def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (i + 1) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)

public def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))


public theorem loop_done (arr : Array Int) (elem : Int) (pos : Int) :
    (∀ j, j < arr.size → (arr[j]! = elem) → (j : Int) ≤ pos) →
    (pos ≥ 0 →
        arr[pos.toNat]! = elem ∧
          (arr.toList.drop (pos.toNat + 1)).all (· ≠ elem)) ∧
    (pos = -1 → arr.toList.all (· ≠ elem)):= by 
sorry


end tmp_lemma_11403