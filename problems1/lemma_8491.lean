import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  True

def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  if a.size ≤ 1 then
    false
  else
    let withIndices := a.mapIdx (fun i x => (i, x))
    withIndices.any (fun (i, x) =>
      i < a.size - 1 && x + 1 == a[i+1]!)

@[reducible, simp]
def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) (h_precond : containsConsecutiveNumbers_precond (a)) :=
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result


theorem any_eq_true_iff_exists (as : Array (Nat × Int)) (p : Nat × Int → Bool) :
    as.any p = true ↔ ∃ i, i < as.size ∧ p (as[i]!) = true:= by 
codetic?(config := { enableGrind := false })


end tmp