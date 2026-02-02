import Codetic
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


theorem last_char_of_repr (n : Nat) (h : n ≠ 0) :
    (String.toList (Nat.repr n)).get! ((String.toList (Nat.repr n)).length - 1)
        = Char.ofNat (Char.toNat '0' + n % 10):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp