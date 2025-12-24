import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  True

def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  a * b < 0

@[reducible, simp]
def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)


theorem mul_lt_zero_implies_opposite_sign
  (a b : Int)
  (h : a * b < 0) :
    (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0):= by 
  aesop?


end tmp