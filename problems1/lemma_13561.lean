import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  True

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0

@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)


theorem LinearSearch_result_le_size (a : Array Int) (e : Int)
    (h_precond : LinearSearch_precond a e) :
    LinearSearch a e h_precond ≤ a.size:= by 
aesop


end tmp