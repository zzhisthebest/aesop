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


theorem insert_pairwise (x : Int) (ys : List Int) (h : List.Pairwise (· ≤ ·) ys) :
    List.Pairwise (· ≤ ·) (insertionSort.insert x ys):= by
induction ys using tmp.insertionSort.insert.induct x
· unfold tmp.insertionSort.insert
  simp_all only [List.Pairwise.nil, List.pairwise_cons, List.not_mem_nil, false_implies, implies_true, and_self]
· unfold tmp.insertionSort.insert
  simp_all only [List.pairwise_cons, ↓reduceIte, List.mem_cons, forall_eq_or_imp, true_and, implies_true, and_self,
    and_true]
  intro a a_1
  obtain ⟨left, right⟩ := h
  grind
· unfold tmp.insertionSort.insert
  simp_all only [Int.not_le, List.pairwise_cons, forall_const]
  obtain ⟨left, right⟩ := h
  split
  next y ys' h ih1
    h_1 =>
    simp_all only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, true_and, implies_true, and_self, and_true]
    intro a a_1
    grind
  next y ys' h ih1 h_1 =>
    simp_all only [Int.not_le, List.pairwise_cons, and_true]
    intro a' a
    induction ys' using tmp.insertionSort.insert.induct x
    · unfold tmp.insertionSort.insert at ih1
      unfold tmp.insertionSort.insert at a
      simp_all only [List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil, List.pairwise_cons, and_self,
        List.mem_cons, or_false]
      subst a
      omega
    · unfold tmp.insertionSort.insert at ih1
      unfold tmp.insertionSort.insert at a
      simp_all only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons, ↓reduceIte, true_and, implies_true,
        and_self, and_true]
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right⟩ := right
      cases a with
      | inl h_1 =>
        subst h_1
        omega
      | inr h_2 =>
        cases h_2 with
        | inl h_1 =>
          subst h_1
          simp_all only
        | inr h_3 => simp_all only
    · unfold tmp.insertionSort.insert at ih1
      unfold tmp.insertionSort.insert at a
      simp_all only [Int.not_le, List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
        List.pairwise_cons]
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right⟩ := right
      split at ih1
      next y_1 ys' h_1 h_2 =>
        split at a
        next
          h_3 =>
          simp_all only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, true_and, implies_true, and_self,
            and_true]
          cases a with
          | inl h_2 =>
            subst h_2
            omega
          | inr h_4 =>
            cases h_4 with
            | inl h_2 =>
              subst h_2
              simp_all only
            | inr h_5 => simp_all only
        next h_3 => simp_all only
      next y_1 ys' h_1 h_2 =>
        split at a
        next h_3 => simp_all only [not_true_eq_false]
        next h_3 =>
          simp_all only [not_false_eq_true, List.pairwise_cons, Int.not_le, List.mem_cons]
          obtain ⟨left_2, right_2⟩ := ih1
          cases a with
          | inl h_2 =>
            subst h_2
            simp_all only
          | inr h_3 => grind
aesop?(config := { enableGrind := false })


end tmp
--提不出来simp定理
