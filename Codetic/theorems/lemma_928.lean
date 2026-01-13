module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_928
public def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

public def isArmstrong_precond (n : Nat) : Prop :=
  True

public def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0

public def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  let k := countDigits n
  sumPowers n k = n

public def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))


public theorem foldl_pow (l : List Nat) (k : Nat) :
    List.foldl (fun acc d => acc + d ^ k) 0 l = (l.map (fun d => d ^ k)).sum:= by 
sorry


end tmp_lemma_928