import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList

def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Array Nat :=
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

@[reducible]
def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)


theorem while_merge_preserves_pairwise
    (a1 a2 : Array Nat) (i j : Nat) (res : Array Nat) :
    List.Pairwise (· ≤ ·) res.toList →
    (∀ k < i, ∀ l < j,
        a1[k]! ≤ a2[l]!) →
    List.Pairwise (· ≤ ·)
      ((Id.run (do
          let mut ii := i
          let mut jj := j
          let mut r := res
          while ii < a1.size ∧ jj < a2.size do
            if a1[ii]! ≤ a2[jj]! then
              r := r.push a1[ii]!
              ii := ii + 1
            else
              r := r.push a2[jj]!
              jj := jj + 1
          return r)).toList):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp