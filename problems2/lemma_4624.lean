import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums

def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  let n := nums.length
  let expectedSum := (n * (n + 1)) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum

@[reducible]
def missingNumber_postcond (nums : List Nat) (result: Nat) (h_precond : missingNumber_precond (nums)) : Prop :=
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums


theorem exactly_one_missing (l : List Nat) (n : Nat) :
    l.all (fun x ↦ x ≤ n) ∧ List.Nodup l ∧ l.length = n →
      ∃ m, m ∈ List.range (n + 1) ∧ m ∉ l ∧
           ∀ x, x ∈ List.range (n + 1) → x ≠ m → x ∈ l:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp