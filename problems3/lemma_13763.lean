import Codetic
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


theorem sum_succ_eq (k : Nat) (h : sumOfSquaresOfFirstNOddNumbers_precond k) :
    sumOfSquaresOfFirstNOddNumbers (k + 1) h
      = sumOfSquaresOfFirstNOddNumbers k h + (2 * (k + 1) - 1) * (2 * (k + 1) - 1):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp