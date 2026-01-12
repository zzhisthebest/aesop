import Aesop
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


theorem sup_mem_or_zero (l : List Nat) :
    l.foldr max 0 ∈ l ∨ l = [] ∧ l.foldr max 0 = 0:= by
induction l with
| @nil => simp_all only [List.foldr_nil, List.not_mem_nil, and_self, or_true]
| @cons a
  a_1 =>
  simp_all only [List.foldr_cons, List.mem_cons, reduceCtorEq, Nat.max_eq_zero_iff, false_and, or_false]
  rename_i tail_ih
  cases tail_ih with
  | inl h => grind
  | inr h_1 => simp_all only [List.foldr_nil, Nat.zero_le, Nat.max_eq_left, List.not_mem_nil, or_false]
aesop?(config := { enableGrind := false })


end tmp
