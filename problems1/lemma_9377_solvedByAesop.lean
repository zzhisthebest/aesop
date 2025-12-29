import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  True

def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  n % 2 == 0

@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)


theorem bool_eq_true_imp_eq {b : Bool} (h : b) : b = true:= by 
aesop


end tmp