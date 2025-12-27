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


theorem new_current_ge_left {c x : Int} :
    (if h : c > x then c else x) ≥ c:= by 
aesop


end tmp