module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_8628
public def sumOfDigits_precond (n : Nat) : Prop :=
  True

public def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  let rec loop (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc
    else loop (n / 10) (acc + n % 10)
  loop n 0

public def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0


public theorem lastChar_of_repr (n : Nat) (h : 0 < n) :
    (String.toList (Nat.repr n)).getLast? = some (Char.ofNat ((n % 10) + Char.toNat '0')):= by 
sorry


end tmp_lemma_8628