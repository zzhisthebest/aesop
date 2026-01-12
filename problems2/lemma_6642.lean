import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def singleDigitPrimeFactor_precond (n : Nat) : Prop :=
  True

def singleDigitPrimeFactor (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  if n == 0 then 0
  else if n % 2 == 0 then 2
  else if n % 3 == 0 then 3
  else if n % 5 == 0 then 5
  else if n % 7 == 0 then 7
  else 0

@[reducible, simp]
def singleDigitPrimeFactor_postcond (n : Nat) (result: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Prop :=
  result ∈ [0, 2, 3, 5, 7] ∧
  (result = 0 → (n = 0 ∨ [2, 3, 5, 7].all (n % · ≠ 0))) ∧
  (result ≠ 0 → n ≠ 0 ∧ n % result == 0 ∧ (List.range result).all (fun x => x ∈ [2, 3, 5, 7] → n % x ≠ 0))


theorem five_mem_list : (5 : Nat) ∈ [0, 2, 3, 5, 7]:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp