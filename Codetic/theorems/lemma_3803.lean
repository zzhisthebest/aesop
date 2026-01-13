module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_3803
public def mergeSort_precond (list : List Int) : Prop :=
  True

public def mergeSort (list : List Int) (h_precond : mergeSort_precond (list)) : List Int :=

  let rec insert (x : Int) (sorted : List Int) : List Int :=
    match sorted with
    | [] => [x]
    | y :: ys =>
        if x ≤ y then
          x :: sorted
        else
          y :: insert x ys
  termination_by sorted.length

  let rec sort (l : List Int) : List Int :=
    match l with
    | [] => []
    | x :: xs =>
        let sortedRest := sort xs
        insert x sortedRest
  termination_by l.length

  sort list

public def mergeSort_postcond (list : List Int) (result: List Int) (h_precond : mergeSort_precond (list)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm list result


public theorem perm_of_mem {a : Int} {l₁ l₂ : List Int}
    (h : List.isPerm l₁ l₂) (ha : a ∈ l₁) : a ∈ l₂:= by 
sorry


end tmp_lemma_3803