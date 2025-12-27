import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = e

def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  linearSearchAux a e 0

@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)


theorem linearSearchAux_eq_min (a : Array Int) (e : Int) {n i : Nat}
    (hle : n ≤ i)
    (hsize : i < a.size)
    (heq : a[i]! = e)
    (hprev : ∀ k, n ≤ k → k < i → a[k]! ≠ e) :
    linearSearchAux a e n = i:= by 
aesop


end tmp