import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2

def mergeSortedLists (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : List Int :=
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

@[reducible]
def mergeSortedLists_postcond (arr1 : List Int) (arr2 : List Int) (result: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result


theorem pairwise_append_of_pairwise {l₁ l₂ : List Int}
    (h₁ : List.Pairwise (· ≤ ·) l₁) (h₂ : List.Pairwise (· ≤ ·) l₂)
    (hsep : ∀ a ∈ l₁, ∀ b ∈ l₂, a ≤ b) :
    List.Pairwise (· ≤ ·) (l₁ ++ l₂):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp