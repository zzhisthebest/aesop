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


theorem UpdateElements_get_other (a : Array Int)
    (h_precond : UpdateElements_precond a) (i : Nat)
    (hi : i < a.size) (hneq4 : i ≠ 4) (hneq7 : i ≠ 7) :
    (UpdateElements a h_precond)[i]! = a[i]!:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp