module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10329
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


public theorem idxOf_zero_eq_len_nonZeros (arr : Array Int) :
    (let nz := arr.toList.filter (· ≠ 0)
     let zs := arr.toList.filter (· = 0)
     (nz ++ zs).idxOf (0 : Int)) = (arr.toList.filter (· ≠ 0)).length:= by 
sorry


end tmp_lemma_10329