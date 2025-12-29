import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  let n := a.size + b.size
  let rec loop (i : Nat) (c : Array Int) : Array Int :=
    if i < n then
      let value := if i < a.size then a[i]! else b[i - a.size]!
      loop (i + 1) (c.set! i value)
    else
      c
  loop 0 (Array.mkArray n 0)

@[reducible, simp]
def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : concat_precond (a) (b)) :=
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)


theorem size_set (c : Array Int) (i : Nat) (v : Int) :
    (c.set! i v).size = c.size:= by 
aesop


end tmp