import Codetic
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


theorem size_set! {α} (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp