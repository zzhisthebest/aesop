import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def TestArrayElements_precond (a : Array Int) (j : Nat) : Prop :=
  j < a.size

def TestArrayElements (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) : Array Int :=
  a.set! j 60

@[reducible, simp]
def TestArrayElements_postcond (a : Array Int) (j : Nat) (result: Array Int) (h_precond : TestArrayElements_precond (a) (j)) :=
  (result[j]! = 60) ∧ (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)


theorem get_set_eq (a : Array Int) (j : Nat) (v : Int) (h : j < a.size) :
    (a.set! j v)[j]! = v:= by 
aesop


end tmp