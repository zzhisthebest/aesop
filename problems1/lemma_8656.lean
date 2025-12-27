import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def sumOfDigits_precond (n : Nat) : Prop :=
  True

def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  let rec loop (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc
    else loop (n / 10) (acc + n % 10)
  loop n 0

@[reducible, simp]
def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0


theorem loop_step (n acc : Nat) :
    (if n = 0 then acc else (let n' := n / 10; let acc' := acc + n % 10; acc')) =
    (if n = 0 then acc else acc + n % 10):= by 
aesop


end tmp