module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_1541
public def lengthOfLIS_precond (nums : List Int) : Prop :=
  True

public def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0

public def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  if nums.isEmpty then 0
  else
    let n := nums.length
    Id.run do
      let mut dp : Array Nat := Array.mkArray n 1

      for i in [1:n] do
        for j in [0:i] do
          if nums[j]! < nums[i]! && dp[j]! + 1 > dp[i]! then
            dp := dp.set! i (dp[j]! + 1)

      maxInArray dp

public def lengthOfLIS_postcond (nums : List Int) (result: Nat) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)


public theorem dp_ne_empty (nums : List Int) (h : ¬ nums.isEmpty) :
    (Id.run do
      let n := nums.length
      let mut dp : Array Nat := Array.mkArray n 1
      pure dp).size > 0:= by 
sorry


end tmp_lemma_1541