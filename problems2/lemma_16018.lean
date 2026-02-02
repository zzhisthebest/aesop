import Codetic
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


theorem swap_neq (X Y : Int) (h : Swap_precond X Y) :
    X ≠ Y → (Swap X Y h).fst ≠ X ∧ (Swap X Y h).snd ≠ Y:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp