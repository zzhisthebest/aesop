import Aesop
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


theorem DoubleQuadruple_snd_eq_four_mul (x : Int) (h : DoubleQuadruple_precond x) :
    (DoubleQuadruple x h).snd = 4 * x:= by 
aesop


end tmp