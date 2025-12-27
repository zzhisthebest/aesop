import Aesop
set_option maxHeartbeats 0
namespace tmp
def swapFirstAndLast_precond (a : Array Int) : Prop :=
  a.size > 0

def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  let first := a[0]!
  let last := a[a.size - 1]!
  a.set! 0 last |>.set! (a.size - 1) first

@[reducible, simp]
def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) (h_precond: swapFirstAndLast_precond a) : Prop :=
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)


theorem inner_unchanged (a : Array Int) (first last : Int) (i : Nat)
    (hi : i + 1 < a.size - 1) :
    ((a.set! 0 last).set! (a.size - 1) first)[i + 1]! = a[i + 1]!:= by 
aesop


end tmp