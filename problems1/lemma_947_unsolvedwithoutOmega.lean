import Aesop
set_option maxHeartbeats 0
namespace tmp
def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  True

def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0

def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  let k := countDigits n
  sumPowers n k = n

@[reducible]
def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))


theorem sumPowers_unfold (n k : Nat) :
    sumPowers n k = sumPowers n k:= by 
aesop?(config := { enableGrind := false })


end tmp