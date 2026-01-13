module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12108
public def CalSum_precond (N : Nat) : Prop :=
  True

public def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N

public def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  2 * result = N * (N + 1)


public theorem mul_succ_succ (n : Nat) :
    n.succ * (n.succ + 1) = n * (n + 1) + 2 * (n + 1):= by 
sorry


end tmp_lemma_12108