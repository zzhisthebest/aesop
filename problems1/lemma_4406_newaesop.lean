import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def minimumRightShifts_precond (nums : List Int) : Prop :=
  List.Nodup nums

def minimumRightShifts (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) : Int :=
  let n := nums.length
  if n <= 1 then 0 else

  let rec isSortedAux (l : List Int) : Bool :=
    match l with
    | [] => true
    | [_] => true
    | x :: y :: xs => if x <= y then isSortedAux (y :: xs) else false

  if isSortedAux nums then 0 else

  let rightShiftOnce (l : List Int) : List Int :=
     match l.reverse with
     | [] => []
     | last :: revInit => last :: revInit.reverse

  let rec checkShifts (shifts_count : Nat) (current_list : List Int) : Int :=
    if shifts_count >= n then -1
    else
      if isSortedAux current_list then
        (shifts_count : Int)
      else
        checkShifts (shifts_count + 1) (rightShiftOnce current_list)
  termination_by n - shifts_count

  checkShifts 1 (rightShiftOnce nums)

@[reducible, simp]
def minimumRightShifts_postcond (nums : List Int) (result: Int) (h_precond : minimumRightShifts_precond (nums)) : Prop :=
  let n := nums.length

  let isSorted (l : List Int) := List.Pairwise (· ≤ ·) l
  let rightShift (k : Nat) (l : List Int) := l.rotateRight k

  if n <= 1 then result = 0 else

  (result ≥ 0 ∧
   result < n ∧
   isSorted (rightShift result.toNat nums) ∧
   (List.range result.toNat |>.all (fun j => ¬ isSorted (rightShift j nums)))
  ) ∨

  (result = -1 ∧
   (List.range n |>.all (fun k => ¬ isSorted (rightShift k nums)))
  )


theorem rightShiftOnce_eq_rotateRight_one (l : List Int) :
    (by
      let rightShiftOnce (l : List Int) : List Int :=
        match l.reverse with
        | [] => []
        | last :: revInit => last :: revInit.reverse
      exact rightShiftOnce l) = l.rotateRight 1:= by 
  aesop?


end tmp