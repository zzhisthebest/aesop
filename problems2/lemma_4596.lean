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


theorem missingNumber_eq_difference (nums : List Nat) (h₁ : List.Nodup nums)
    (h₂ : ∀ x, x ∈ nums → x ∈ List.range (nums.length + 1)) :
    let n := nums.length
    let expected := (n * (n + 1)) / 2
    let actual   := nums.foldl (· + ·) 0
    expected - actual ∈ List.range (n + 1) ∧
    ¬(expected - actual ∈ nums) ∧
    ∀ x, (x ∈ List.range (n + 1)) → x ≠ (expected - actual) → x ∈ nums:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp