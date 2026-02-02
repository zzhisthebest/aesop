import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def isPowerOfTwo_precond (n : Int) : Prop :=
  True

def isPowerOfTwo (n : Int) (h_precond : isPowerOfTwo_precond (n)) : Bool :=
  if n <= 0 then false
  else
    let rec aux (m : Int) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if m = 1 then true
      else if m % 2 ≠ 0 then false
      else aux (m / 2) (fuel - 1)
    aux n n.natAbs

def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1
  | n+1 => base * pow base n

@[reducible]
def isPowerOfTwo_postcond (n : Int) (result: Bool) (h_precond : isPowerOfTwo_precond (n)) : Prop :=
  if result then ∃ (x : Nat), (pow 2 x = n) ∧ (n > 0)
  else ¬ (∃ (x : Nat), (pow 2 x = n) ∧ (n > 0))


theorem pow_two_pos (k : Nat) : pow 2 k > 0:= by 
codetic?(config := { enableGrind := false })


end tmp