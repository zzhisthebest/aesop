module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_13863
public def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  True

public def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  let rec loop (k : Nat) (sum : Nat) : Nat :=
    if k = 0 then
      sum
    else
      loop (k - 1) (sum + (2 * k - 1) * (2 * k - 1))
  loop n 0

public def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :=
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0


public theorem mul_div_cancel_three (n : Nat) :
    (n * (2 * n - 1) * (2 * n + 1)) / 3 *
      3 = n * (2 * n - 1) * (2 * n + 1):= by 
sorry


end tmp_lemma_13863