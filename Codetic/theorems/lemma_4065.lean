module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_4065
public def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList

public def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Array Nat :=
  Id.run <| do
    let mut i := 0
    let mut j := 0
    let mut result := #[]
    while i < a1.size ∧ j < a2.size do
      if a1[i]! ≤ a2[j]! then
        result := result.push a1[i]!
        i := i + 1
      else
        result := result.push a2[j]!
        j := j + 1
    while i < a1.size do
      result := result.push a1[i]!
      i := i + 1
    while j < a2.size do
      result := result.push a2[j]!
      j := j + 1
    return result

public def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)


public theorem while_copy_a1_preserves_perm
    (a1 : Array Nat) (i : Nat) (res : Array Nat) :
    res.toList.isPerm (a1.toList.take i) →
    ((Id.run (do
        let mut ii := i
        let mut r := res
        while ii < a1.size do
          r := r.push a1[ii]!
          ii := ii + 1
        return r)).toList).isPerm (a1.toList):= by 
sorry


end tmp_lemma_4065