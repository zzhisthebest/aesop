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


theorem foldl_max_eq_foldl_max_of_map (l : List (List Int)) :
    l.foldl (fun acc s => max acc s.length) 0 =
      (l.map List.length).foldl max 0:= by 
  aesop?


end tmp