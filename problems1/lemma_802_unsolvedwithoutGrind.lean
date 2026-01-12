import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  True

def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
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

@[reducible]
def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result


theorem pairwise_cons_cons_of_le
    {x y : Int} {ys : List Int}
    (hxy : x ≤ y)
    (hpair : List.Pairwise (· ≤ ·) (y :: ys)) :
    List.Pairwise (· ≤ ·) (x :: y :: ys):= by 
aesop?(config := { enableGrind := false })


end tmp