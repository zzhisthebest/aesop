module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_3829
public def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2

public def mergeSortedLists (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : List Int :=
  let rec merge (xs : List Int) (ys : List Int) : List Int :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xt, y :: yt =>
      if x <= y then
        x :: merge xt (y :: yt)
      else
        y :: merge (x :: xt) yt

  merge arr1 arr2

public def mergeSortedLists_postcond (arr1 : List Int) (arr2 : List Int) (result: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result


public theorem pairwise_merge_of_sorted {l₁ l₂ : List Int}
    (h₁ : List.Pairwise (· ≤ ·) l₁) (h₂ : List.Pairwise (· ≤ ·) l₂) :
    List.Pairwise (· ≤ ·) (List.merge l₁ l₂):= by 
sorry


end tmp_lemma_3829