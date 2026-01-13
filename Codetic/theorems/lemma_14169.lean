module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14169
public def Match_precond (s : String) (p : String) : Prop :=
  s.toList.length = p.toList.length

public def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  let sList := s.toList
  let pList := p.toList
  let rec loop (i : Nat) : Bool :=
    if i < sList.length then
      if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
      else loop (i + 1)
    else true
  loop 0

public def Match_postcond (s : String) (p : String) (result: Bool) (h_precond : Match_precond (s) (p)) :=
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))


public theorem cond_true_iff {c₁ c₂ : Char} :
    ((c₁ ≠ c₂) ∧ (c₂ ≠ '?')) = false ↔ (c₁ = c₂) ∨ (c₂ = '?'):= by 
sorry


end tmp_lemma_14169