import Aesop
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


theorem exists_iff_any_true (a : Array Int) (h : ¬ a.size ≤ 1) :
    (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i+1]!) ↔
      ((a.mapIdx (fun i x => (i, x))).any
        (fun p : Nat × Int => p.1 < a.size - 1 && p.2 + 1 == a[p.1 + 1]!)):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp