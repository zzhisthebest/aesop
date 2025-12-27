import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  True

def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  let rec loop (k : Nat) (sum : Nat) : Nat :=
    if k = 0 then
      sum
    else
      loop (k - 1) (sum + (2 * k - 1) * (2 * k - 1))
  loop n 0

@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :=
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0


theorem succ_ne_zero (n : Nat) : n.succ ≠ 0 := Nat.succ_ne_zero _

@[simp] theorem succ_sub_one (n : Nat) : n.succ - 1 = n := Nat.succ_sub_one _

@[simp] theorem two_mul_succ (n : Nat) : 2 * n.succ = 2 * n + 2:= by 
aesop


end tmp