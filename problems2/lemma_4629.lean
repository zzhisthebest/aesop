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


theorem sum_of_list_eq_expected_minus_missing
    {nums : List Nat} {n m : Nat}
    (h_len : nums.length = n)
    (h_nodup : List.Nodup nums)
    (h_subset : ∀ x ∈ nums, x ∈ List.range (n + 1))
    (h_missing : m ∈ List.range (n + 1) ∧ m ∉ nums) :
    (nums.foldl (· + ·) 0) = ((n * (n + 1)) / 2) - m:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp