import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  True

def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else x

@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)


theorem Abs_eq_neg_of_lt (x : Int) (hx : x < 0) (h : Abs_precond x) :
    Abs x h = -x:= by 
codetic?(config := { enableGrind := false })


end tmp