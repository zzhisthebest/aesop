import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  True

def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
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

@[reducible]
def lengthOfLIS_postcond (nums : List Int) (result: Nat) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

attribute [aesop simp]
-- List.foldl_toArray'
-- List.foldl_nil
-- List.mem_toArray
-- List.not_mem_nil
-- List.size_toArray
-- List.length_nil
Array.size_eq_zero_iff
theorem maxInArray_mem_or_zero (arr : Array Nat) :
    arr.size = 0 → maxInArray arr = 0 ∧ ∀ x ∈ arr, x ≤ maxInArray arr:= by
  -- intro a
  -- simp_all only [Array.size_eq_zero_iff, maxInArray, ge_iff_le, List.size_toArray, List.length_nil,
  --   List.foldl_toArray', List.foldl_nil, List.mem_toArray, List.not_mem_nil, Nat.le_zero_eq, false_implies,
  --   implies_true, and_self]
  intro a
  simp_all only [Array.size_eq_zero_iff, maxInArray]
  subst a
  apply And.intro
  · rfl
  · intro x a
    grind


end tmp
