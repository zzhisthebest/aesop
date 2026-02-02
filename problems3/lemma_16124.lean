import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def SwapBitvectors_precond (X : UInt8) (Y : UInt8) : Prop :=
  True

def SwapBitvectors (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) : UInt8 × UInt8 :=
  let temp := X.xor Y
  let newY := temp.xor Y
  let newX := temp.xor newY
  (newX, newY)

@[reducible, simp]
def SwapBitvectors_postcond (X : UInt8) (Y : UInt8) (result: UInt8 × UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :=
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)


theorem fst_swapped (X Y : UInt8) (h : SwapBitvectors_precond X Y) :
    (SwapBitvectors X Y h).fst = Y:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp