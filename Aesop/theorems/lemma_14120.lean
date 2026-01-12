module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14120
public def append_precond (a : Array Int) (b : Int) : Prop :=
  True

public def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc

public def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  let c_initial := copy a 0 (Array.empty)
  let c_full := c_initial.push b
  c_full

public def append_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : append_precond (a) (b)) :=
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1


public theorem push_preserves_get (a : Array Int) (b : Int) (i : Nat) (h : i < a.size) :
    (a.push b)[i]! = a[i]!:= by 
sorry


end tmp_lemma_14120