module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_1876
public def longestIncreasingStreak_precond (nums : List Int) : Prop :=
  True

public def longestIncreasingStreak (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) : Nat :=
  let rec aux (lst : List Int) (prev : Option Int) (currLen : Nat) (maxLen : Nat) : Nat :=
    match lst with
    | [] => max currLen maxLen
    | x :: xs =>
      match prev with
      | none => aux xs (some x) 1 (max 1 maxLen)
      | some p =>
        if x > p then aux xs (some x) (currLen + 1) (max (currLen + 1) maxLen)
        else aux xs (some x) 1 (max currLen maxLen)
  aux nums none 0 0

public def longestIncreasingStreak_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingStreak_precond (nums)) : Prop :=
  (nums = [] → result = 0) ∧

  (result > 0 →
    (List.range (nums.length - result + 1) |>.any (fun start =>
      start + result ≤ nums.length ∧
      (List.range (result - 1) |>.all (fun i =>
        nums[start + i]! < nums[start + i + 1]!)) ∧
      (start = 0 ∨ nums[start - 1]! ≥ nums[start]!) ∧
      (start + result = nums.length ∨ nums[start + result - 1]! ≥ nums[start + result]!)))) ∧

  (List.range (nums.length - result) |>.all (fun start =>
    List.range result |>.any (fun i =>
      start + i + 1 ≥ nums.length ∨ nums[start + i]! ≥ nums[start + i + 1]!)))


public theorem start_in_range (nums : List Int) (s r : Nat) (hfit : s + r ≤ nums.length) :
    s ∈ List.range (nums.length - r + 1):= by 
sorry


end tmp_lemma_1876