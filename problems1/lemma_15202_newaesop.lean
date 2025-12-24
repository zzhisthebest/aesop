import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def remove_front_precond (a : Array Int) : Prop :=
  a.size > 0

def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc

def remove_front (a : Array Int) (h_precond : remove_front_precond (a)) : Array Int :=
  if a.size > 0 then
    let c := copyFrom a 1 (Array.mkEmpty (a.size - 1))
    c
  else
    panic "Precondition violation: array is empty"

@[reducible, simp]
def remove_front_postcond (a : Array Int) (result: Array Int) (h_precond : remove_front_precond (a)) :=
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)


theorem remove_front_postcond_snd (a : Array Int) (h : remove_front_precond a) :
    (remove_front a h).size = a.size - 1:= by 
  aesop?


end tmp