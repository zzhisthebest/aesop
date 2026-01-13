module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_4746
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


public theorem sum_eq_range_minus_missing (l : List Nat) (h_all : l.all (· ≤ l.length))
    (h_nodup : List.Nodup l) :
    ∃ m, m ∈ List.range (l.length + 1) ∧
      m ∉ l ∧
      l.sum = (List.range (l.length + 1)).sum - m:= by 
sorry


end tmp_lemma_4746