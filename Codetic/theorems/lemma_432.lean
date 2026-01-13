module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_432
public def firstDuplicate_precond (lst : List Int) : Prop :=
  True

public def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Int :=
  let rec helper (seen : List Int) (rem : List Int) : Int :=
    match rem with
    | [] => -1
    | h :: t => if seen.contains h then h else helper (h :: seen) t
  helper [] lst

public def firstDuplicate_postcond (lst : List Int) (result: Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  (result = -1 → List.Nodup lst) ∧
  (result ≠ -1 →
    lst.count result > 1 ∧
    (lst.filter (fun x => lst.count x > 1)).head? = some result
  )


public theorem count_cons_self (a b : Int) (l : List Int) :
    (a :: l).count b = (if a = b then 1 else 0) + l.count b:= by 
sorry


end tmp_lemma_432