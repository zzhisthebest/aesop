import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def BubbleSort_precond (a : Array Int) : Prop :=
  True

def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a

def BubbleSort (a : Array Int) (h_precond : BubbleSort_precond (a)) : Array Int :=
  if a.size = 0 then a else bubbleOuter (a.size - 1) a

@[reducible, simp]
def BubbleSort_postcond (a : Array Int) (result: Array Int) (h_precond : BubbleSort_precond (a)) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm result.toList a.toList


theorem BubbleSort_isPerm (a : Array Int) (h : BubbleSort_precond a) :
    List.isPerm (BubbleSort a h).toList a.toList:= by 
  aesop?


end tmp