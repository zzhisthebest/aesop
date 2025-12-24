import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def mergeSort_precond (list : List Int) : Prop :=
  True

def mergeSort (list : List Int) (h_precond : mergeSort_precond (list)) : List Int :=

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

@[reducible, simp]
def mergeSort_postcond (list : List Int) (result: List Int) (h_precond : mergeSort_precond (list)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm list result


theorem perm_cons {a b : Int} {l₁ l₂ : List Int} :
    List.isPerm (a :: l₁) (b :: l₂) ↔ a = b ∧ List.isPerm l₁ l₂ ∨
                                   a ≠ b ∧ List.isPerm (a :: l₁) l₂ ∧ List.isPerm [] (b :: l₂):= by 
  aesop?


end tmp