import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isPerfectSquare_precond (n : Nat) : Prop :=
  True

def isPerfectSquare (n : Nat) : Bool :=
  if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n

@[reducible, simp]
def isPerfectSquare_postcond (n : Nat) (result : Bool) : Prop :=
  result ↔ ∃ i : Nat, i * i = n


theorem sq_lt_succ (i n : Nat) (hi : i * i = n) : i < n + 1:= by 
codetic?(config := { enableGrind := false })


end tmp