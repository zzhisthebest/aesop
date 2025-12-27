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


theorem index_valid {arr : Array Int} {i : Nat} (h : i < arr.size) :
    i < arr.size := h


@[simp] theorem get_eq_get! (arr : Array Int) (i : Nat) (h : i < arr.size) :
    arr[i]! = arr.get! i := rfl


@[simp] theorem toNat_eq_of_eq {a b : Int} (h : a = b) : a.toNat = b.toNat:= by 
aesop


end tmp