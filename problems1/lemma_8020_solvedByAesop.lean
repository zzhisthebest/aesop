import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def UpdateElements_precond (a : Array Int) : Prop :=
  a.size ≥ 8

def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2

@[reducible, simp]
def UpdateElements_postcond (a : Array Int) (result: Array Int) (h_precond : UpdateElements_precond (a)) :=
  result[4]! = (a[4]!) + 3 ∧
  result[7]! = 516 ∧
  (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)


theorem get_two_sets_eq (a : Array Int) (i j k : Nat) (v₁ v₂ : Int)
    (hi : i = j) (hk : k ≠ j) (hj : j < a.size) (hk' : k < a.size) :
    ((a.set! j v₁).set! k v₂)[i]! = v₁:= by 
aesop


end tmp