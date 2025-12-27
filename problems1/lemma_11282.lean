import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  True

def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    let prev := sumOfFourthPowerOfOddNumbers n h_precond
    let nextOdd := 2 * n + 1
    prev + nextOdd^4

@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)


theorem rhs_succ (n : Nat) :
    (n.succ) * (2 * n.succ + 1) *
      (7 + 24 * n.succ ^ 3 - 12 * n.succ ^ 2 - 14 * n.succ) =
      n * (2 * n + 1) *
          (7 + 24 * n ^ 3 - 12 * n ^ 2 - 14 * n) +
        15 * (2 * n + 1) ^ 4:= by 
aesop


end tmp