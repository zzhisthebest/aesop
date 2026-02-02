import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def reverse_precond (a : Array Int) : Prop :=
  True

def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr

def reverse (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
  reverse_core a 0

@[reducible, simp]
def reverse_postcond (a : Array Int) (result: Array Int) (h_precond : reverse_precond (a)) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)


@[simp]
theorem get_set!_ne (arr : Array Int) {i j : Nat} (hi : i < arr.size) (hj : j < arr.size)
    (hij : i ≠ j) (v : Int) :
    (arr.set! i v)[j]! = arr[j]!:= by 
codetic?(config := { enableGrind := false })


end tmp