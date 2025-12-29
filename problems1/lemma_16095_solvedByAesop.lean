import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  True

def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := y2 + x2
  (x3, y2)

@[reducible, simp]
def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)


theorem y2_is_X (X Y : Int) :
    (let x1 := X; let y1 := Y; let x2 := y1 - x1; let y2 := y1 - x2; y2) = X:= by 
aesop


end tmp