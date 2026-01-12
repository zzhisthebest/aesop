module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_4623
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


public theorem foldl_eq_of_all (l : List Nat) (p : Nat → Bool) :
    l.all p → l.foldl (· + ·) 0 = (l.filter (fun x ↦ p x = true)).foldl (· + ·) 0:= by 
sorry


end tmp_lemma_4623