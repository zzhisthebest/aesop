import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Nat :=
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

@[reducible, simp]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)


theorem contains_iff (l : List Nat) (n : Nat) :
    l.contains n = true ↔ n ∈ l:= by 
aesop?(config := { enableGrind := false })


end tmp