import Codetic
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


theorem insert_preserves_pairwise_left
    (x y : Int) (ys : List Int) (hxy : x ≤ y)
    (hys : List.Pairwise (· ≤ ·) (y :: ys)) :
    List.Pairwise (· ≤ ·) (x :: y :: ys):= by
simp_all only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, true_and, implies_true, and_self, and_true]
intro a a_1
obtain ⟨left, right⟩ := hys
clear right
--grind
induction ys with
| @nil => simp_all only [List.not_mem_nil]
| @cons a_2
  a_1_1 =>
  simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp]
  obtain ⟨left, right⟩ := left
  cases a_1 with
  | inl h =>
    subst h
    omega
  | inr h_1 => simp_all only [forall_const]


end tmp
--提不出来simp定理。但没用的right应该clear掉，似乎要实现一种机制才行。
