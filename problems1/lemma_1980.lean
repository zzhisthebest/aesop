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


theorem max_mem_of_mem (l : List Nat) (h : l ≠ []) :
    l.foldl (fun acc n => max acc n) 0 ∈ l:= by 
aesop


end tmp