import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Match_precond (s : String) (p : String) : Prop :=
  s.toList.length = p.toList.length

def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  let sList := s.toList
  let pList := p.toList
  let rec loop (i : Nat) : Bool :=
    if i < sList.length then
      if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
      else loop (i + 1)
    else true
  loop 0

@[reducible, simp]
def Match_postcond (s : String) (p : String) (result: Bool) (h_precond : Match_precond (s) (p)) :=
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))


theorem lt_or_eq_of_le_len {l : List α} {i : Nat}
    (h : i ≤ l.length) : i < l.length ∨ i = l.length:= by 
aesop


end tmp