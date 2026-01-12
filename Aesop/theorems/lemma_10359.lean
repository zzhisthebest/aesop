module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10359
public def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  True

public def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  let nonZeros := arr.toList.filter (· ≠ 0)
  let zeros := arr.toList.filter (· = 0)
  Array.mk (nonZeros ++ zeros)

public def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :=
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)


public theorem drop_from_first_zero (arr : Array Int) :
    (arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0)).drop
        ((arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0)).idxOf 0) =
      arr.toList.filter (· = 0):= by 
sorry


end tmp_lemma_10359