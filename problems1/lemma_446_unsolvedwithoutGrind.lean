import Aesop
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


theorem filter_head?_eq_some_of_mem
    {p : Int → Bool} {l : List Int} {x : Int}
    (hx : x ∈ l) (hpx : p x = true) :
    (l.filter p).head? = some x ∨ (l.filter p).head? ≠ some x:= by
aesop?(config := { enableGrind := false })


end tmp
