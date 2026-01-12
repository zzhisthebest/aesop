import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def majorityElement_precond (xs : List Nat) : Prop :=
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)

def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  let rec countOccurrences (target : Nat) (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | y :: ys =>
      if y = target then 1 + countOccurrences target ys
      else countOccurrences target ys

  let rec findCandidate (lst : List Nat) (candidate : Option Nat) (count : Nat) : Nat :=
    match lst with
    | [] =>
      match candidate with
      | some c => c
      | none => 0
    | x :: xs =>
      match candidate with
      | some c =>
        if x = c then
          findCandidate xs (some c) (count + 1)
        else if count = 0 then
          findCandidate xs (some x) 1
        else
          findCandidate xs (some c) (count - 1)
      | none =>
        findCandidate xs (some x) 1

  let cand := findCandidate xs none 0
  cand

@[reducible]
def majorityElement_postcond (xs : List Nat) (result: Nat) (h_precond : majorityElement_precond (xs)) : Prop :=
  let count := xs.count result
  count > xs.length / 2


theorem any_iff_exists_gt (xs : List Nat) :
    xs.any (fun x => xs.count x > xs.length / 2) = true ↔
    ∃ m, xs.count m > xs.length / 2:= by
simp_all only [gt_iff_lt, List.any_eq_true, decide_eq_true_eq]
apply Iff.intro
intro a
obtain ⟨w, h⟩ := a
obtain ⟨left, right⟩ := h
grind
intro a
obtain ⟨w, h⟩ := a
apply Exists.intro
apply And.intro
on_goal 2 => exact h
induction xs
simp_all only [List.length_nil, Nat.zero_div, List.count_nil, Nat.lt_irrefl]
simp_all only [List.length_cons, List.count_cons, beq_iff_eq, List.mem_cons]
split at h
rename_i tail_ih h_1
on_goal 2 => rename_i tail_ih h_1
subst h_1
simp_all only [true_or]
simp_all only [Nat.add_zero]
grind


end tmp
