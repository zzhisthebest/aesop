import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def longestIncreasingSubsequence_precond (numbers : List Int) : Prop :=
  True

def longestIncreasingSubsequence (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Nat :=
  let rec buildTables : List Int → List Int → List Nat → Nat → Nat
    | [], _, lengths, _ =>
        let rec findMaxLength : List Nat → Nat
          | [] => 0
          | x :: xs =>
              let maxRest := findMaxLength xs
              if x > maxRest then x else maxRest
        findMaxLength lengths
    | currNum :: restNums, prevNums, lengths, idx =>
        let rec findLengthEndingAtCurr : List Int → List Nat → Nat → Nat
          | [], _, best => best
          | prevVal :: restVals, prevLen :: restLens, best =>
              if prevVal < currNum then
                findLengthEndingAtCurr restVals restLens (max best prevLen)
              else
                findLengthEndingAtCurr restVals restLens best
          | _, _, best => best

        let bestPrevLen := findLengthEndingAtCurr prevNums lengths 0
        let currLength := bestPrevLen + 1
        buildTables restNums (prevNums ++ [currNum]) (lengths ++ [currLength]) (idx + 1)

  match numbers with
  | [] => 0
  | [x] => 1
  | first :: rest => buildTables rest [first] [1] 1

@[reducible, simp]
def longestIncreasingSubsequence_postcond (numbers : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Prop :=
  let allSubseq := (numbers.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)


theorem List.all_le_iff_forall (l : List Nat) (n : Nat) :
    l.all (· ≤ n) ↔ ∀ m ∈ l, m ≤ n:= by 
aesop


end tmp