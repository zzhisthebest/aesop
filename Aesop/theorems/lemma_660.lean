module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_660
public def ifPowerOfFour_precond (n : Nat) : Prop :=
  True

public def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
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

public def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)


public theorem div_four_lt {n : Nat} (h : n % 4 = 0) (h0 : n ≠ 0) : n / 4 < n:= by 
sorry


end tmp_lemma_660