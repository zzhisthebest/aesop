import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  True

def semiOrderedPermutation (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
  let lengthList := nums.length
  let numOne : Int := 1
  let largestNum : Int := Int.ofNat lengthList

  let firstIndex := nums.idxOf numOne
  let lastIndex := nums.idxOf largestNum

  let startPosition := 0
  let endPosition := lengthList - 1

  let shouldMoveOne := firstIndex != startPosition
  let shouldMoveLast := lastIndex != endPosition

  let distanceOne := if shouldMoveOne then firstIndex else 0
  let distanceLast := if shouldMoveLast then endPosition - lastIndex else 0

  let totalMoves := distanceOne + distanceLast
  let needAdjustment := firstIndex > lastIndex
  let adjustedMoves := if needAdjustment then totalMoves - 1 else totalMoves

  adjustedMoves

@[reducible]
def semiOrderedPermutation_postcond (nums : List Int) (result: Int) (h_precond : semiOrderedPermutation_precond (nums)) : Prop :=
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n = result + 2 + posn
  else
    pos1 + n = result + 1 + posn


theorem if_ne_eq_sub (a b : Nat) : (if a ≠ b then b - a else 0) = b - a:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp