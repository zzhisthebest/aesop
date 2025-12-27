import Aesop
set_option maxHeartbeats 0
namespace tmp
def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none

@[reducible, simp]
def findProduct_precond (lst : List Int) : Prop :=
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)

def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => lst[ei]! * lst[oi]!
  | none => 0

@[reducible, simp]
def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True


theorem findProduct_eq_of_some (lst : List Int) (h_precond : findProduct_precond lst)
    (ei oi : Nat) (h : firstEvenOddIndices lst = some (ei, oi)) :
    findProduct lst h_precond = lst[ei]! * lst[oi]!:= by 
aesop


end tmp