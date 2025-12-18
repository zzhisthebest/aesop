import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def removeDuplicates_precond (nums : List Int) : Prop :=
  List.Pairwise (· ≤ ·) nums

def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  match nums with
  | [] =>
    0
  | h :: t =>
    let init := h
    let initCount := 1
    let rec countUniques (prev : Int) (xs : List Int) (k : Nat) : Nat :=
      match xs with
      | [] =>
        k
      | head :: tail =>
        let isDuplicate := head = prev
        if isDuplicate then
          countUniques prev tail k
        else
          let newK := k + 1
          countUniques head tail newK
    countUniques init t initCount

@[reducible]
def removeDuplicates_postcond (nums : List Int) (result: Nat) (h_precond : removeDuplicates_precond (nums)) : Prop :=
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result


theorem eq_of_mem_of_pairwise {a b : Int} {l : List Int}
    (hpair : List.Pairwise (· ≤ ·) (a :: b :: l)) (hmem : a ∈ b :: l) : a = b:= by
  simp_all only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
  obtain ⟨left, right⟩ := hpair
  obtain ⟨left, right_1⟩ := left
  obtain ⟨left_1, right⟩ := right
  cases hmem with
  | inl h =>
    subst h
    simp_all only [implies_true, Int.le_refl]
  | inr h_1 => grind


end tmp
