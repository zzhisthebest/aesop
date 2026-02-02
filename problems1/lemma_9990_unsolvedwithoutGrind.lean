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


theorem middle_unchanged (a : Array Int) (v1 v2 : Int) (i : Nat)
    (h₁ : i + 1 < a.size - 1) :
    ((a.set! 0 v2).set! (a.size - 1) v1)[i + 1]! = a[i + 1]!:= by
have h1:0≠i+1:=by codetic
have h1:a.size - 1≠i+1:=by codetic

codetic?(config := { enableGrind := false })
end tmp
--这个题的问题和定理无关
