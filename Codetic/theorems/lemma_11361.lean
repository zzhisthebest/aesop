module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11361
public def isEven (n : Int) : Bool :=
  n % 2 = 0

public def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

public def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none

public def findProduct_precond (lst : List Int) : Prop :=
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)

public def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => lst[ei]! * lst[oi]!
  | none => 0

public def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True


public theorem findIdx?_some_of_exists {l : List Int} {p : Int → Bool}
    (h : ∃ x ∈ l, p x) : ∃ i, l.findIdx? p = some i:= by 
sorry


end tmp_lemma_11361