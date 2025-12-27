import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def maxArray_precond (a : Array Int) : Prop :=
  a.size > 0

def maxArray_aux (a : Array Int) (index : Nat) (current : Int) : Int :=
  if index < a.size then
    let new_current := if current > a[index]! then current else a[index]!
    maxArray_aux a (index + 1) new_current
  else
    current

def maxArray (a : Array Int) (h_precond : maxArray_precond (a)) : Int :=
  maxArray_aux a 1 a[0]!

@[reducible, simp]
def maxArray_postcond (a : Array Int) (result: Int) (h_precond : maxArray_precond (a)) :=
  (∀ (k : Nat), k < a.size → result >= a[k]!) ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)


theorem maxArray_aux_correct
    (a : Array Int) (idx cur : Int) (i : Nat) (h_le : i ≤ a.size)
    (h_cur : ∀ j, j < i → a[j]! ≤ cur) :
    (∀ k, k < a.size → a[k]! ≤ maxArray_aux a i cur) ∧
      (∃ k, k < a.size ∧ maxArray_aux a i cur = a[k]!):= by 
aesop


end tmp