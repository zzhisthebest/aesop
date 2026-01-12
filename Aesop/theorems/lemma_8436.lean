module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_8436
public def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  True

public def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  if a.size ≤ 1 then
    false
  else
    let withIndices := a.mapIdx (fun i x => (i, x))
    withIndices.any (fun (i, x) =>
      i < a.size - 1 && x + 1 == a[i+1]!)

public def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) (h_precond : containsConsecutiveNumbers_precond (a)) :=
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result


public theorem any_iff_exists_consecutive (a : Array Int) (h : 1 < a.size) :
    (a.mapIdx (fun i x => (i, x))).any (fun (i, x) =>
        i < a.size - 1 && x + 1 == a[i+1]!) = true ↔
      ∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!:= by 
sorry


end tmp_lemma_8436