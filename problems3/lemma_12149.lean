import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  True

def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N

@[reducible, simp]
def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  2 * result = N * (N + 1)


theorem CalSum_succ (N : Nat) (h : CalSum_precond (Nat.succ N)) :
    CalSum (Nat.succ N) h = Nat.succ N + CalSum N (by trivial):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp