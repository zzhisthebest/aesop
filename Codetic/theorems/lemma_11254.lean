module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11254
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


public theorem succ_pow_five (n : Nat) :
    (n + 1) ^ 5 =
      n ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 10 * n ^ 2 + 5 * n + 1:= by 
sorry


end tmp_lemma_11254