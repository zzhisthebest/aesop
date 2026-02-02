import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  True

def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  let a := 2 * x
  let b := 2 * a
  (a, b)

@[reducible, simp]
def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  result.fst = 2 * x ∧ result.snd = 2 * result.fst


theorem let_a_eq (x : Int) : (let a := 2 * x; a) = 2 * x:= by 
codetic?(config := { enableGrind := false })


end tmp