import Aesop
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


theorem int_mod_eq_zero_iff (n : Int) : (n % 8 == 0) = true ↔ n % 8 = 0:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp