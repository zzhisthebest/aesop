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


theorem min?_eq_some (xs : List Nat) (r : Nat) :
    xs.min? = some r ↔ r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x):= by 
aesop


end tmp