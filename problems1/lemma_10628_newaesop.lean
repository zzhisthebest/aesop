import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0

@[reducible, simp]
def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :=
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))


theorem Array.le_of_index_le_index {arr : Array Int}
    (h : findFirstOccurrence_precond arr target) {i j : Nat}
    (hi : i < arr.size) (hj : j < arr.size) (hij : i ≤ j) :
    arr[i]! ≤ arr[j]!:= by 
  aesop?


end tmp