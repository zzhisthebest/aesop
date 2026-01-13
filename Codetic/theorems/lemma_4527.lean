module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_4527
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


public theorem diff_not_mem (nums : List Nat) (h_all : nums.all (· ≤ nums.length))
    (h_nodup : List.Nodup nums) :
    let n := nums.length
    let expected := (n * (n + 1)) / 2
    let actual   := nums.foldl (· + ·) 0
    let diff := expected - actual
    diff ∉ nums:= by 
sorry


end tmp_lemma_4527