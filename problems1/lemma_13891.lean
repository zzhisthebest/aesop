import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  ∃ i, i < a.size ∧ P (a[i]!)

def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if P (a[n]!) then n else loop (n + 1)
    else
      0
  loop 0

@[reducible, simp]
def LinearSearch3_postcond (a : Array Int) (P : Int -> Bool) (result: Nat) (h_precond : LinearSearch3_precond (a) (P)) :=
  result < a.size ∧ P (a[result]!) ∧ (∀ k, k < result → ¬ P (a[k]!))


theorem if_lt_true {a : Array Int} {n : Nat} (h : n < a.size) :
    (if n < a.size then (True) else False) = True:= by 
aesop


end tmp