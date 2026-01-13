module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11155
public def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  a.size > 0

public def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
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

public def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) (h_precond : hasOnlyOneDistinctElement_precond (a)) :=
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))


public theorem exists_diff_imp_any (a : Array Int) (h : ∃ i, i < a.size ∧ a[i]! ≠ a[0]!) :
    (a.toList).any (fun x => x ≠ a.toList[0]!):= by 
sorry


end tmp_lemma_11155