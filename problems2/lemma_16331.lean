import Codetic
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


theorem SwapSimultaneous_imp (X Y : Int)
    (h : SwapSimultaneous_precond X Y) :
    (X ≠ Y →
      (SwapSimultaneous X Y h).fst ≠ X ∧ (SwapSimultaneous X Y h).snd ≠ Y):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp