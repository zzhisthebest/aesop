import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def secondSmallest_precond (s : Array Int) : Prop :=
  s.size > 1

def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i

def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  let (minIdx, secondIdx) :=
    if s[1]! < s[0]! then (1, 0) else (0, 1)
  secondSmallestAux s 2 minIdx secondIdx

@[reducible, simp]
def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)


theorem secondSmallest_is_elem
  (s : Array Int) (h : secondSmallest_precond s) :
    secondSmallest s h ∈ s:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp