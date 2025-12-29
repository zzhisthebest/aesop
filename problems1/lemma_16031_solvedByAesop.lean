import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Swap_precond (X : Int) (Y : Int) : Prop :=
  True

def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  let x := X
  let y := Y
  let tmp := x
  let x := y
  let y := tmp
  (x, y)

@[reducible, simp]
def Swap_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : Swap_precond (X) (Y)) :=
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)


theorem Swap_snd (X Y : Int) (h_precond : Swap_precond X Y) :
    (Swap X Y h_precond).snd = X:= by 
aesop


end tmp