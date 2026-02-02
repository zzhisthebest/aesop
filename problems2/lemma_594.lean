import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  True

def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  let rec helper (n : Nat) : Bool :=
    match n with
    | 0 =>
      false
    | Nat.succ m =>
      match m with
      | 0 =>
        true
      | Nat.succ l =>
        if (l+2)%4=0 then
          helper ((l+2)/4)
        else
          false
  helper n

@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)


theorem mod4_eq_zero_iff (k : Nat) :
    k % 4 = 0 ↔ ∃ q, k = 4 * q:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp