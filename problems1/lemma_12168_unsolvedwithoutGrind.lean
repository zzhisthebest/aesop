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


theorem succ_mul_eq (n m : Nat) : (Nat.succ n) * m = n * m + m:= by 
aesop?(config := { enableGrind := false })


end tmp