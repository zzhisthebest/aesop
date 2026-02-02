import Codetic
set_option maxHeartbeats 0
namespace tmp
def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

@[reducible, simp]
def countDigits_precond (s : String) : Prop :=
  True

def countDigits (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  List.length (List.filter isDigit s.toList)

@[reducible, simp]
def countDigits_postcond (s : String) (result: Nat) (h_precond : countDigits_precond (s)) :=
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0


theorem sub_eq_zero_of_eq' {n m : Nat} (h : n = m) : m - n = 0:= by 
codetic?(config := { enableGrind := false })


end tmp