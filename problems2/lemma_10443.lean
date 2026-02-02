import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  True

def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  let nonZeros := arr.toList.filter (· ≠ 0)
  let zeros := arr.toList.filter (· = 0)
  Array.mk (nonZeros ++ zeros)

@[reducible, simp]
def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :=
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)


theorem take_drop_at_idx (l : List Int) :
    let nz := l.filter (· ≠ 0)
    let zs := l.filter (· = 0)
    let i  := (nz ++ zs).idxOf 0
    (nz ++ zs).take i = nz ∧ (nz ++ zs).drop i = zs:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp