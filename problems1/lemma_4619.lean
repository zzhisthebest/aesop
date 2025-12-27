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


theorem missing_eq_expected_minus_actual
    (nums : List Nat) (h : missingNumber_precond nums) :
    let n := nums.length
    let exp := (n * (n + 1)) / 2
    let act := nums.foldl (· + ·) 0
    ∃ m, m = exp - act ∧
          m ∈ List.range (n + 1) ∧
          m ∉ nums ∧
          ∀ x, x ∈ List.range (n + 1) → x ≠ m → x ∈ nums:= by 
aesop


end tmp