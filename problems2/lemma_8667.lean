import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isSorted_precond (a : Array Int) : Prop :=
  True

def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  if a.size ≤ 1 then
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[i + 1])
      else
        true) |>.all id

@[reducible, simp]
def isSorted_postcond (a : Array Int) (result: Bool) (h_precond : isSorted_precond (a)) :=
  (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result


theorem forall_of_size_le_one (a : Array Int) (h : a.size ≤ 1) :
    (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp