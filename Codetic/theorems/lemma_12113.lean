module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12113
public def CalSum_precond (N : Nat) : Prop :=
  True

public def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N

public def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  2 * result = N * (N + 1)


public theorem succ_mul_succ_succ (n : Nat) :
    (n + 1) * (n + 2) = 2 * (n + 1) + n * (n + 1):= by 
sorry


end tmp_lemma_12113