import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  a.size > 0

def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  if a.size = 0 then
    true
  else
    let firstElement := a[0]!
    let rec loop (i : Nat) : Bool :=
      if h : i < a.size then
        if a[i]! = firstElement then loop (i + 1) else false
      else
        true
    loop 1

@[reducible, simp]
def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) (h_precond : hasOnlyOneDistinctElement_precond (a)) :=
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))


theorem postcond_any (a : Array Int) (hpre : hasOnlyOneDistinctElement_precond a) :
    (hasOnlyOneDistinctElement a hpre = false) →
      (a.toList).any (fun x => x ≠ (a.toList)[0]!):= by 
aesop


end tmp