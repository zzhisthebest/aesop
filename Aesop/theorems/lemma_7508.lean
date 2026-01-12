module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_7508
public def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  True

public def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  a * b < 0

public def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)


public theorem cond_iff_mul_lt_zero (a b : Int) :
    ((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) ↔ a * b < 0:= by 
sorry


end tmp_lemma_7508