module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_5716
public def removeDuplicates_precond (nums : List Int) : Prop :=
  List.Pairwise (· ≤ ·) nums

public def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  match nums with
  | [] =>
    0
  | h :: t =>
    let init := h
    let initCount := 1
    let rec countUniques (prev : Int) (xs : List Int) (k : Nat) : Nat :=
      match xs with
      | [] =>
        k
      | head :: tail =>
        let isDuplicate := head = prev
        if isDuplicate then
          countUniques prev tail k
        else
          let newK := k + 1
          countUniques head tail newK
    countUniques init t initCount

public def removeDuplicates_postcond (nums : List Int) (result: Nat) (h_precond : removeDuplicates_precond (nums)) : Prop :=
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result


public theorem sorted_head_not_mem_tail {a b : Int} {t : List Int}
    (hpair : List.Pairwise (· ≤ ·) (a :: b :: t))
    (hneq : a ≠ b) :
    a ∉ b :: t:= by 
sorry


end tmp_lemma_5716