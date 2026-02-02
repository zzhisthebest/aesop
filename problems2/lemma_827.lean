import Codetic
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


theorem le_of_mem_of_pairwise {l : List Int} (h : List.Pairwise (· ≤ ·) l) :
    ∀ {a}, a ∈ l → (l.headD 0) ≤ a:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp