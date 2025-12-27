import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def insertionSort_precond (l : List Int) : Prop :=
  True

def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)

def insertionSort (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  let result := sortList l
  result

@[reducible]
def insertionSort_postcond (l : List Int) (result: List Int) (h_precond : insertionSort_precond (l)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result


theorem insertElement_eq_cons_cons (x y : Int) (ys : List Int) (hxy : x ≤ y) :
    insertElement x (y :: ys) = x :: y :: ys:= by 
aesop


end tmp