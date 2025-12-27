import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (i + 1) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)

@[reducible, simp]
def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))


theorem not_elem_after_strict (arr : Array Int) (elem : Int) (h : lastPosition_precond arr elem)
    {i : Nat} (hi : i < arr.size) (hgt : elem < arr[i]!) :
    ∀ {j}, i < j → j < arr.size → arr[j]! ≠ elem:= by 
aesop


end tmp