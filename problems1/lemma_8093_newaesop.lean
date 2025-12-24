import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def arraySum_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

def arraySum (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) : Array Int :=
  if a.size ≠ b.size then
    panic! "Array lengths mismatch"
  else
    let n := a.size;
    let c := Array.mkArray n 0;
    let rec loop (i : Nat) (c : Array Int) : Array Int :=
      if i < n then
        let c' := c.set! i (a[i]! + b[i]!);
        loop (i + 1) c'
      else c;
    loop 0 c

@[reducible, simp]
def arraySum_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arraySum_precond (a) (b)) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → a[i]! + b[i]! = result[i]!)


theorem arraySum_elementwise (a b : Array Int) (h : arraySum_precond a b) :
    ∀ i, i < a.size → a[i]! + b[i]! = (arraySum a b h)[i]!:= by 
  aesop?


end tmp