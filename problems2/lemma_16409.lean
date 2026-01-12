import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def SwapSimultaneous_precond (X : Int) (Y : Int) : Prop :=
  True

def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  (Y, X)

@[reducible, simp]
def SwapSimultaneous_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :=
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)


theorem precond_true (X Y : Int) (h : SwapSimultaneous_precond X Y) : True:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp