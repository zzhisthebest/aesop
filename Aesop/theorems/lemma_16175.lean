module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_16175
public def iter_copy_precond (s : Array Int) : Prop :=
  True

public def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc
    else
      acc
  loop 0 Array.empty

public def iter_copy_postcond (s : Array Int) (result: Array Int) (h_precond : iter_copy_precond (s)) :=
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)


public theorem get_append_right (a b : Array Int) (i : Nat) (hi : a.size ≤ i)
    (hib : i - a.size < b.size) :
    (a ++ b)[i]! = b[i - a.size]!:= by 
sorry


end tmp_lemma_16175