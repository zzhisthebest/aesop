module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11584
public def isPerfectSquare_precond (n : Nat) : Prop :=
  True

public def isPerfectSquare (n : Nat) : Bool :=
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

public def isPerfectSquare_postcond (n : Nat) (result : Bool) : Prop :=
  result ↔ ∃ i : Nat, i * i = n


public theorem lt_one_add_of_sq_eq (n i : Nat) (h : i * i = n) : i < n + 1:= by 
sorry


end tmp_lemma_11584