import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True

def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c

@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)


theorem not_and_iff_or_not (p q : Prop) : ¬ (p ∧ q) ↔ (¬ p ∨ ¬ q):= by
simp_all only [not_and]
apply Iff.intro
· intro a
  aesop?(config:={enableGrind:=false})
· intro a a_1
  simp_all only [not_true_eq_false, false_or, not_false_eq_true]


end tmp
