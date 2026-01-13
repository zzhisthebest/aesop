module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_843
public def insertionSort_precond (l : List Int) : Prop :=
  True

public def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

public def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)

public def insertionSort (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  let result := sortList l
  result

public def insertionSort_postcond (l : List Int) (result: List Int) (h_precond : insertionSort_precond (l)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result


public theorem perm_swap (a b : Int) (l : List Int) :
    List.isPerm (a :: b :: l) (b :: a :: l):= by 
sorry


end tmp_lemma_843