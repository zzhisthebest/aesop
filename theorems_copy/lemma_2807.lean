module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_2807
public def maxOfList_precond (lst : List Nat) : Prop :=
  lst ≠ []

public def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  let rec helper (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | [x] => x
    | x :: xs =>
      let maxTail := helper xs
      if x > maxTail then x else maxTail
  helper lst

public def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result


public theorem le_of_if_pos {c d : Nat} (h : c > d) : max c d = c:= by 
sorry


end tmp_lemma_2807