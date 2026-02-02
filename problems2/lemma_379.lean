import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def firstDuplicate_precond (lst : List Int) : Prop :=
  True

def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Int :=
  let rec helper (seen : List Int) (rem : List Int) : Int :=
    match rem with
    | [] => -1
    | h :: t => if seen.contains h then h else helper (h :: seen) t
  helper [] lst

@[reducible]
def firstDuplicate_postcond (lst : List Int) (result: Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  (result = -1 → List.Nodup lst) ∧
  (result ≠ -1 →
    lst.count result > 1 ∧
    (lst.filter (fun x => lst.count x > 1)).head? = some result
  )


theorem contains_eq_mem (a : Int) (l : List Int) :
    l.contains a = true ↔ a ∈ l:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp