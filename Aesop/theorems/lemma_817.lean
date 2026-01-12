module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_817
public def insertionSort_precond (xs : List Int) : Prop :=
  True

public def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
    let rec insert (x : Int) (ys : List Int) : List Int :=
      match ys with
      | []      => [x]
      | y :: ys' =>
        if x <= y then
          x :: y :: ys'
        else
          y :: insert x ys'

    let rec sort (arr : List Int) : List Int :=
      match arr with
      | []      => []
      | x :: xs => insert x (sort xs)

    sort xs

public def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result


public theorem cons_perm (x : Int) (ys : List Int) :
    List.isPerm (x :: ys) (x :: ys):= by 
sorry


end tmp_lemma_817