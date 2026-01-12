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


theorem eq_imp_bool_eq (a : Int) (h : a = 0) : a % 2 == 0:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp