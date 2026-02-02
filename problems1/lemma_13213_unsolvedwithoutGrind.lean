import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def SquareRoot_precond (N : Nat) : Prop :=
  True

def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r
    | bound+1, r =>
        if (r + 1) * (r + 1) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0

@[reducible, simp]
def SquareRoot_postcond (N : Nat) (result: Nat) (h_precond : SquareRoot_precond (N)) :=
  result * result ≤ N ∧ N < (result + 1) * (result + 1)


theorem succ_mul_succ (r : Nat) : (r+1)*(r+1) = r*r + 2*r + 1:= by 
codetic?(config := { enableGrind := false })


end tmp