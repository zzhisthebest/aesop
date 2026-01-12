module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11666
public def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0

public def findFirstOdd_precond (a : Array Int) : Prop :=
  a.size > 0

public def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  let indexed := a.toList.zipIdx

  let found := List.find? (fun (x, _) => isOdd x) indexed

  Option.map (fun (_, i) => i) found

public def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)


public theorem mem_zipIdx_iff (a : Array Int) (x : Int) (i : Nat) :
    (x, i) ∈ a.toList.zipIdx ↔ i < a.size ∧ a[i]? = some x:= by 
sorry


end tmp_lemma_11666