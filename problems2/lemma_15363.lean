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


theorem swap_correct (a : Array Int) (i j : Nat) (hji : j = a.size - 1 - i)
    (hi : i < a.size) (hj : j < a.size) :
    let t   := a[i]!
    let a₁ := a.set! i (a[j]!)
    let a₂ := a₁.set! j t
    (a₂[i]! = a[j]!) ∧ (a₂[j]! = a[i]!) ∧
    ∀ k, k ≠ i → k ≠ j → a₂[k]! = a[k]!:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp