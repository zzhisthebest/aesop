module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_13213
public def SquareRoot_precond (N : Nat) : Prop :=
  True

public def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r
    | bound+1, r =>
        if (r + 1) * (r + 1) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0

public def SquareRoot_postcond (N : Nat) (result: Nat) (h_precond : SquareRoot_precond (N)) :=
  result * result ≤ N ∧ N < (result + 1) * (result + 1)


public theorem succ_mul_succ (r : Nat) : (r+1)*(r+1) = r*r + 2*r + 1:= by 
sorry


end tmp_lemma_13213