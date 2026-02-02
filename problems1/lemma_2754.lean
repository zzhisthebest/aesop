import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LongestIncreasingSubsequence_precond (a : Array Int) : Prop :=
  True

def intMax (x y : Int) : Int :=
  if x < y then y else x

def LongestIncreasingSubsequence (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Int :=
  let n := a.size
  let dp := Id.run do
    let mut dp := Array.mkArray n 1
    for i in [1:n] do
      for j in [0:i] do
        if a[j]! < a[i]! then
          let newVal := intMax (dp[i]!) (dp[j]! + 1)
          dp := dp.set! i newVal
    return dp
  match dp with
  | #[] => 0
  | _   => dp.foldl intMax 0

@[reducible, simp]
def LongestIncreasingSubsequence_postcond (a : Array Int) (result: Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Prop :=
  let allSubseq := (a.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)


theorem intMax_le_intMax_of_le_right
    {a b c : Int} (hb : (0 : Int) ≤ b) (hbc : b ≤ c) :
    intMax a b ≤ intMax a c:= by 
codetic?(config := { enableGrind := false })


end tmp