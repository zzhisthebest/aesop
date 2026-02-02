import Codetic
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


theorem b_pos_of_mul_neg_of_a_neg {a b : Int}
    (ha : a < 0) (h : a * b < 0) : 0 < b:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp