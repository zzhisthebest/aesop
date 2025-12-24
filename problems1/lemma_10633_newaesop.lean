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


theorem findFirstOccurrence_correct
    (arr : Array Int) (target : Int) (h_pre : findFirstOccurrence_precond arr target) :
    let r := findFirstOccurrence arr target h_pre
    (r ≥ 0 →
        arr[r.toNat]! = target ∧
        (∀ i : Nat, i < r.toNat → arr[i]! ≠ target)) ∧
      (r = -1 →
        (∀ i : Nat, i < arr.size → arr[i]! ≠ target)):= by 
  aesop?


end tmp