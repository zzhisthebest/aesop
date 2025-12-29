import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  True

def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  n % 10

@[reducible, simp]
def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)


theorem mod_nonneg (n : Nat) : 0 ≤ n % 10:= by 
aesop


end tmp