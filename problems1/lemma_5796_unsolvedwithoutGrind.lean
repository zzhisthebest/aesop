import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  True

def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  let rec helper (lst : List Nat) (target : Nat) : List Nat :=
    match lst with
    | [] => []
    | x :: xs =>
      let rest := helper xs target
      if x = target then rest else x :: rest
  helper lst target

@[reducible]
def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat) (h_precond : removeElement_precond (lst) (target)): Prop :=

  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length


theorem get_eq_of_mem_zipIdx (l : List Nat) (x : Nat) (i : Nat)
    (hmem : (x,i) ∈ l.zipIdx) : l[i]? = some x:= by 
aesop?(config := { enableGrind := false })


end tmp