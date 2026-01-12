module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_4602
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


public theorem precond_implies_subset_and_card (nums : List Nat)
    (h : missingNumber_precond nums) :
    nums ⊆ List.range (nums.length + 1) ∧
    nums.length = (List.range (nums.length + 1)).length - 1:= by 
sorry


end tmp_lemma_4602