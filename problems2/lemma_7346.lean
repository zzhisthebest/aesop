import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def uniqueSorted_precond (arr : List Int) : Prop :=
  True

def uniqueSorted (arr : List Int) (h_precond : uniqueSorted_precond (arr)) : List Int :=
  let rec insert (x : Int) (sorted : List Int) : List Int :=
  match sorted with
  | [] =>
    [x]
  | head :: tail =>
    if x <= head then
      x :: head :: tail
    else
      head :: insert x tail

let rec insertionSort (xs : List Int) : List Int :=
  match xs with
  | [] =>
    []
  | h :: t =>
    let sortedTail := insertionSort t
    insert h sortedTail

let removeDups : List Int → List Int
| xs =>
  let rec aux (remaining : List Int) (seen : List Int) (acc : List Int) : List Int :=
    match remaining with
    | [] =>
      acc.reverse
    | h :: t =>
      if h ∈ seen then
        aux t seen acc
      else
        aux t (h :: seen) (h :: acc)
  aux xs [] []

insertionSort (removeDups arr)

@[reducible, simp]
def uniqueSorted_postcond (arr : List Int) (result: List Int) (h_precond : uniqueSorted_precond (arr)) : Prop :=
  List.isPerm arr.eraseDups result ∧ List.Pairwise (· ≤ ·) result


theorem uniqueSorted_perm (arr : List Int) (h : uniqueSorted_precond arr) :
    List.isPerm arr.eraseDups (uniqueSorted arr h):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp