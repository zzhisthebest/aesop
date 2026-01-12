module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_4681
public def missingNumber_precond (nums : List Nat) : Prop :=
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums

public def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  let n := nums.length
  let expectedSum := (n * (n + 1)) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum

public def missingNumber_postcond (nums : List Nat) (result: Nat) (h_precond : missingNumber_precond (nums)) : Prop :=
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums


public theorem exists_unique_missing
    (nums : List Nat) (h : missingNumber_precond nums) :
    ∃ m, m ∈ List.range (nums.length + 1) ∧ m ∉ nums ∧
         ∀ x, x ∈ List.range (nums.length + 1) → x ≠ m → x ∈ nums:= by 
sorry


end tmp_lemma_4681