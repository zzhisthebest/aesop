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


theorem loop_terminates_mem (a : Array Int) (i : Nat) (cur : Int) :
    i = a.size →
    (∃ k, k < i ∧ cur = a[k]!) →
    ∃ k, k < a.size ∧ loop a i cur = a[k]!:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp