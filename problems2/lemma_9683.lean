import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  k < s.size

def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  s.eraseIdx! k

@[reducible, simp]
def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)


theorem eraseIdx!_get_right (s : Array Int) (k i : Nat) (h₁ : k < s.size)
    (h₂ : i < (s.eraseIdx! k).size) (h₃ : k ≤ i) :
    (s.eraseIdx! k)[i]! = s[i+1]!:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp