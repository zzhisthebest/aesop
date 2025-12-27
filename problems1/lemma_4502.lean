import Aesop
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


theorem missing_is_unique (nums : List Nat) (h : missingNumber_precond nums) :
    let n := nums.length
    let expected := (n * (n + 1)) / 2
    let actual   := nums.foldl (· + ·) 0
    let missing  := expected - actual
    missing ∈ List.range (n + 1) ∧
    ¬ missing ∈ nums ∧
    ∀ x, x ∈ List.range (n + 1) → x ≠ missing → x ∈ nums:= by 
aesop


end tmp