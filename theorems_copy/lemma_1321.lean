module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_1321
public def isPowerOfTwo_precond (n : Int) : Prop :=
  True

public def isPowerOfTwo (n : Int) (h_precond : isPowerOfTwo_precond (n)) : Bool :=
  if n <= 0 then false
  else
    let rec aux (m : Int) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if m = 1 then true
      else if m % 2 ≠ 0 then false
      else aux (m / 2) (fuel - 1)
    aux n n.natAbs

public def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1
  | n+1 => base * pow base n

public def isPowerOfTwo_postcond (n : Int) (result: Bool) (h_precond : isPowerOfTwo_precond (n)) : Prop :=
  if result then ∃ (x : Nat), (pow 2 x = n) ∧ (n > 0)
  else ¬ (∃ (x : Nat), (pow 2 x = n) ∧ (n > 0))


public theorem div_two_pos_of_even (m : Int) (hm : 0 < m) (hmod : m % 2 = 0) :
    0 < m / 2 ∧ (m / 2).natAbs < m.natAbs:= by 
sorry


end tmp_lemma_1321