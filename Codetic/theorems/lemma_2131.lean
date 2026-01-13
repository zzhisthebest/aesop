module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_2131
public def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

public def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Nat :=
  let max2 (a : Nat) (b : Nat) : Nat :=
    if a > b then a else b

  let rec listLength (l : List Int) : Nat :=
    match l with
    | []      => 0
    | _ :: xs => 1 + listLength xs

  let rec helper (lst : List Int) (prev : Option Int) : Nat :=
    match lst with
    | [] => 0
    | h :: t =>
        let canTake : Bool :=
          if prev = none then true
          else if prev.get! < h then true else false
        let withTake : Nat :=
          if canTake then 1 + helper t (some h) else 0
        let withoutTake : Nat := helper t prev
        max2 withTake withoutTake

  let result := helper nums none
  result

public def longestIncreasingSubsequence_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)


public theorem max2_eq_max (a b : Nat) :
    (if a > b then a else b) = max a b:= by 
sorry


end tmp_lemma_2131