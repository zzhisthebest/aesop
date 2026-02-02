import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def isItEight_precond (n : Int) : Prop :=
  True

def isItEight (n : Int) (h_precond : isItEight_precond (n)) : Bool :=
  let rec hasDigitEight (m : Nat) : Bool :=
    if m <= 0 then false
    else if m % 10 == 8 then true
    else hasDigitEight (m / 10)
    termination_by m

  let absN := Int.natAbs n
  n % 8 == 0 || hasDigitEight absN

@[reducible]
def isItEight_postcond (n : Int) (result: Bool) (h_precond : isItEight_precond (n)) : Prop :=
  let absN := Int.natAbs n;
  (n % 8 == 0 ∨ ∃ i, absN / (10^i) % 10 == 8) ↔ result


theorem Nat.mod_lt_self (m d : Nat) (h : 0 < d) (h' : m < d) : m % d = m:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp