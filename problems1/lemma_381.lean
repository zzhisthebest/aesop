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


theorem firstDuplicate_result_counts_gt_one
    (lst : List Int) (h : firstDuplicate lst (by trivial) ≠ -1) :
    lst.count (firstDuplicate lst (by trivial)) > 1:= by 
aesop


end tmp