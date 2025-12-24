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


theorem sum_eq_expected_minus_missing {l : List Nat}
    (hbound : l.all (fun x => x ≤ l.length))
    (hnodup : List.Nodup l) :
    ∃ m, (l.foldl (· + ·) 0) = ((l.length * (l.length + 1)) / 2) - m ∧
         m ∈ List.range (l.length + 1) ∧
         m ∉ l ∧
         ∀ x, x ∈ List.range (l.length + 1) → x ≠ m → x ∈ l:= by 
  aesop?


end tmp