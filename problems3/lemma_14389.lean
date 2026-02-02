import Codetic
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


theorem loop_base (a : Array Int) (cur : Int)
    (hsize : a.size ≤ a.size) (hcur_le : ∀ j, j < a.size → cur ≤ a[j]!)
    (hcur_eq : ∃ j, j < a.size ∧ cur = a[j]!) :
    (∀ j, j < a.size → loop a a.size cur ≤ a[j]!) ∧
    (∃ j, j < a.size ∧ loop a a.size cur = a[j]!):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp