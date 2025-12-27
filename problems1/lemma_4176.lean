import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b

def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged

def mergeSorted (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  let merged := mergeSortedAux a b
  merged

@[reducible, simp]
def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) (h_precond : mergeSorted_precond (a) (b)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)


theorem mem_mergeSortedAux {x : Int} {a b : List Int} :
    x ∈ mergeSortedAux a b → x ∈ a ++ b:= by 
aesop


end tmp