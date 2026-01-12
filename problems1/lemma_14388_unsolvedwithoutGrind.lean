import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def minArray_precond (a : Array Int) : Prop :=
  a.size > 0

def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin

def minArray (a : Array Int) (h_precond : minArray_precond (a)) : Int :=
  loop a 1 (a[0]!)

@[reducible, simp]
def minArray_postcond (a : Array Int) (result: Int) (h_precond : minArray_precond (a)) :=
  (∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)


theorem extend_le {a : Array Int} {x : Int}
    (hpref : ∀ j, j < i → x ≤ a[j]!)
    (hwhole : ∀ j, i ≤ j → j < a.size → x ≤ a[j]!)
    : ∀ j, j < a.size → x ≤ a[j]!:= by 
aesop?(config := { enableGrind := false })


end tmp