import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def findSmallest_precond (s : Array Nat) : Prop :=
  True

def findSmallest (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  s.toList.min?

@[reducible, simp]
def findSmallest_postcond (s : Array Nat) (result: Option Nat) (h_precond : findSmallest_precond (s)) :=
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)


theorem cons_min?_neq_none (a : Nat) (l : List Nat) : (a :: l).min? ≠ none:= by 
aesop


end tmp