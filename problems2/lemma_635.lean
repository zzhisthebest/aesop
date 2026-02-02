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


theorem mul_one_lt_mul_four (k : Nat) (hkpos : 0 < k) :
    k * 1 < k * 4:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp