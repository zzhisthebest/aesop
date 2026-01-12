import Aesop
set_option maxHeartbeats 0
namespace tmp
def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0

@[reducible]
def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  d > 0

def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0

def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  let rec go (i acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i'+1 =>
      let acc' := if isSumDivisibleBy i' d then acc + 1 else acc
      go i' acc'
  go n 0

@[reducible]
def countSumDivisibleBy_postcond (n : Nat) (d : Nat) (result: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Prop :=
  (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n))) - result = 0 ∧
  result ≤ (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)))


theorem length_filter_append (p : Nat → Bool) (l : List Nat) (a : Nat) :
    (List.filter p (l ++ [a])).length =
      (List.filter p l).length + (if p a then 1 else 0):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp