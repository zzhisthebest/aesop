import Aesop
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


theorem get_push_eq (as : Array Nat) (x i : Nat) (h : i < as.size) :
    (as.push x)[i]! = as[i]!:= by
simp_all only [Array.getElem!_eq_getD, Nat.default_eq_zero, Array.getD_eq_getD_getElem?, Array.getElem?_push,
  getElem?_pos, getElem!_pos]
split
next h_1 =>
  subst h_1
  simp_all only [Option.getD_some]
  omega
next h_1 => simp_all only [Option.getD_some]


end tmp
