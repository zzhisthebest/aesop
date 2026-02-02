import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def longestIncreasingSubseqLength_precond (xs : List Int) : Prop :=
  True

def subsequences {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let subs := subsequences xs
    subs ++ subs.map (fun s => x :: s)

def isStrictlyIncreasing : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => if x < y then isStrictlyIncreasing (y :: rest) else false

def longestIncreasingSubseqLength (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Nat :=
  let subs := subsequences xs
  let increasing := subs.filter isStrictlyIncreasing
  increasing.foldl (fun acc s => max acc s.length) 0

@[reducible]
def longestIncreasingSubseqLength_postcond (xs : List Int) (result: Nat) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Prop :=
  let allSubseq := (xs.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)


theorem isStrictlyIncreasing_iff_pairwise (l : List Int) :
    isStrictlyIncreasing l = true ↔ List.Pairwise (· < ·) l:= by
apply Iff.intro
· intro a
  induction l with
  | @nil =>
    unfold tmp.isStrictlyIncreasing at a
    simp_all only [List.Pairwise.nil]
  | @cons a_1 a_1_1 =>
    unfold tmp.isStrictlyIncreasing at a
    simp_all only [Bool.if_false_right, List.pairwise_cons]
    apply And.intro
    · intro a' a_2
      split at a
      next tail_ih x heq => simp_all only [reduceCtorEq]
      next tail_ih x head heq => simp_all only [List.cons.injEq, List.Pairwise.nil, implies_true, List.not_mem_nil]
      next tail_ih x x_1 y rest
        heq =>
        simp_all only [List.cons.injEq, Bool.and_eq_true, decide_eq_true_eq, List.pairwise_cons, forall_const,
          List.mem_cons]
        obtain ⟨left, right⟩ := tail_ih
        obtain ⟨left_1, right_1⟩ := heq
        obtain ⟨left_2, right_2⟩ := a
        subst left_1 right_1
        cases a_2 with
        | inl h =>
          subst h
          simp_all only
        | inr h_1 => grind
    · split at a
      next tail_ih x heq => simp_all only [reduceCtorEq]
      next tail_ih x head heq => simp_all only [List.cons.injEq, List.Pairwise.nil]
      next tail_ih x x_1 y rest heq =>
        simp_all only [List.cons.injEq, Bool.and_eq_true, decide_eq_true_eq, List.pairwise_cons, forall_const,
          implies_true, and_self]
· intro a
  induction l using tmp.isStrictlyIncreasing.induct
  · unfold tmp.isStrictlyIncreasing
    simp_all only [List.Pairwise.nil]
  · unfold tmp.isStrictlyIncreasing
    simp_all only [List.pairwise_cons, List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil, and_self]
  · unfold tmp.isStrictlyIncreasing
    simp_all only [List.pairwise_cons, and_imp, List.mem_cons, forall_eq_or_imp, true_and, ↓reduceIte, implies_true]
  · unfold tmp.isStrictlyIncreasing
    simp_all only [Int.not_lt, List.pairwise_cons, List.mem_cons, forall_eq_or_imp, ↓reduceIte]
    obtain ⟨left, right⟩ := a
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left_1, right⟩ := right
    grind
codetic?(config := { enableGrind := false })


end tmp
