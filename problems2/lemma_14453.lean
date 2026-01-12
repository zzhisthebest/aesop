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


theorem loop_inv (a : Array Int) (i : Nat) (currentMin : Int)
    (hi : i ≤ a.size)
    (hbound : ∀ j, j < i → a[j]! ≥ currentMin)
    (hexist : ∃ j, j < i ∧ a[j]! = currentMin) :
    (∀ j, j < a.size → loop a i currentMin ≤ a[j]!) ∧
      (∃ j, j < a.size ∧ loop a i currentMin = a[j]!):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp