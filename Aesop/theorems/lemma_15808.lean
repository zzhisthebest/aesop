module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_15808
public def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0

public def hasCommonElement (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) : Bool :=
  a.any fun x => b.any fun y => x = y

public def hasCommonElement_postcond (a : Array Int) (b : Array Int) (result: Bool) (h_precond : hasCommonElement_precond (a) (b)) :=
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result


public theorem any_nested_outer {a b : Array Int} :
    a.any (fun x => b.any (fun y => x = y)) = true ↔
      ∃ i, i < a.size ∧ (b.any fun y => a[i]! = y) = true:= by 
sorry


end tmp_lemma_15808