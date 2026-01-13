module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11248
public def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  True

public def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    let prev := sumOfFourthPowerOfOddNumbers n h_precond
    let nextOdd := 2 * n + 1
    prev + nextOdd^4

public def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)


public theorem odd_sq (n : Nat) :
    (2 * n + 1) ^ 2 = 4 * n ^ 2 + 4 * n + 1:= by 
sorry


end tmp_lemma_11248