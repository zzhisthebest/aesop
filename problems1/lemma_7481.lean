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


theorem fold_eq_length_filter (n d : Nat)
    (h_precond : countSumDivisibleBy_precond n d) :
    (List.range n).foldl (fun c x => if isSumDivisibleBy x d then c + 1 else c) 0 =
      List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)):= by 
aesop


end tmp