import Codetic
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


theorem loop_returns_first_index
    (arr : Array Int) (target : Int)
    (h_precond : findFirstOccurrence_precond arr target)
    (h_ex : ∃ k, k < arr.size ∧ arr[k]! = target)
    (h_min : ∀ m, m < arr.size → arr[m]! = target → k ≤ m) :
    findFirstOccurrence arr target h_precond = k:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp