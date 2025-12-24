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


theorem not_cond_implies_not_result (a b : Int) (h_precond : hasOppositeSign_precond a b)
    (hnot : ¬ ((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0))) :
    ¬ hasOppositeSign a b h_precond:= by 
  aesop?


end tmp