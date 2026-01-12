module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_5791
public def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  True

public def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  let rec helper (lst : List Nat) (target : Nat) : List Nat :=
    match lst with
    | [] => []
    | x :: xs =>
      let rest := helper xs target
      if x = target then rest else x :: rest
  helper lst target

public def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat) (h_precond : removeElement_precond (lst) (target)): Prop :=

  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length


public theorem filter_length_eq (lst : List Nat) (target : Nat) :
    (lst.filter fun x => x ≠ target).length = lst.length - (lst.count target):= by 
sorry


end tmp_lemma_5791