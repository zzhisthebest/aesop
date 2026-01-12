module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10554
public def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

public def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0

public def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :=
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))


public theorem later_gt (arr : Array Int) (target i : Nat) (hpre : findFirstOccurrence_precond arr (0 : Int))
    (hi : i < arr.size) (hgt : arr[i]! > (target : Int)) :
    ∀ j, i ≤ j → j < arr.size → arr[j]! > (target : Int):= by 
sorry


end tmp_lemma_10554