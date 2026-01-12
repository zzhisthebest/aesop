import Aesop
set_option maxHeartbeats 0
namespace tmp
def isDigit (c : Char) : Bool :=
  (c ≥ '0') && (c ≤ '9')

@[reducible, simp]
def allDigits_precond (s : String) : Prop :=
  True

def allDigits (s : String) (h_precond : allDigits_precond (s)) : Bool :=
  let rec loop (it : String.Iterator) : Bool :=
    if it.atEnd then
      true
    else
      if !isDigit it.curr then
        false
      else
        loop it.next
  loop s.iter

@[reducible, simp]
def allDigits_postcond (s : String) (result: Bool) (h_precond : allDigits_precond (s)) :=
  (result = true ↔ ∀ c ∈ s.toList, isDigit c)


theorem list_fold_and_eq_true {α : Type} (p : α → Bool) (l : List α) :
    (l.foldr (fun a b => p a && b) true = true) ↔ ∀ a ∈ l, p a:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp