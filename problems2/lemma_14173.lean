import Codetic
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


theorem list_length_eq_of_match_precond {s p : String}
    (h : Match_precond s p) :
    s.toList.length = p.toList.length:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp