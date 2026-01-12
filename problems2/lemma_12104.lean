import Aesop
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


theorem two_mul_CalSum (n : Nat) (h : CalSum_precond n) :
    2 * CalSum n h = n * (n + 1):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp