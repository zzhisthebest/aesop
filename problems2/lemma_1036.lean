import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def intMax (x y : Int) : Int :=
  if x < y then y else x

def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  let m := a.size
  let n := b.size

  let dp := Id.run do
    let mut dp := Array.mkArray (m + 1) (Array.mkArray (n + 1) 0)
    for i in List.range (m + 1) do
      for j in List.range (n + 1) do
        if i = 0 ∨ j = 0 then
          ()
        else if a[i - 1]! = b[j - 1]! then
          let newVal := ((dp[i - 1]!)[j - 1]!) + 1
          dp := dp.set! i (dp[i]!.set! j newVal)
        else
          let newVal := intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
          dp := dp.set! i (dp[i]!.set! j newVal)
    return dp
  (dp[m]!)[n]!

@[reducible, simp]
def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Prop :=
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)


theorem get!_zero (i : Nat) (h : i < (Array.mkArray (n := 1) 0).size) :
    (Array.mkArray (n := 1) 0)[i]! = 0:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp