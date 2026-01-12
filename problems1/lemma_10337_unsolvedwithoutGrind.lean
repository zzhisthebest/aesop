import Aesop
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


theorem idxOf_zero_eq_length (l₁ l₂ : List Int)
    (h₁ : ∀ x ∈ l₁, x ≠ (0 : Int))
    (h₂ : ∀ x ∈ l₂, x = (0 : Int)) :
    (l₁ ++ l₂).idxOf 0 = l₁.length:= by 
aesop?(config := { enableGrind := false })


end tmp