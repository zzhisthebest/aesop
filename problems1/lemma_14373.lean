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


theorem loop_inv₂ (a : Array Int) (i : Nat) (cur newCur : Int)
    (h_lt : i < a.size)
    (h_exists : ∃ j, j < i ∧ cur = a[j]!)
    (h_new : newCur = if cur > a[i]! then a[i]! else cur) :
    ∃ j, j < i + 1 ∧ newCur = a[j]!:= by 
aesop


end tmp