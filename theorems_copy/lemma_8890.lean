module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_8890
public def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  True

public def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  let subLen := sub.length
  let mainLen := main.length
  if subLen > mainLen then
    false
  else
    let rec check (i : Nat) : Bool :=
      if i + subLen > mainLen then
        false
      else if sub = (main.drop i).take subLen then
        true
      else if i + 1 ≤ mainLen then
        check (i + 1)
      else
        false
    termination_by mainLen - i
    check 0

public def isSublist_postcond (sub : List Int) (main : List Int) (result: Bool) (h_precond : isSublist_precond (sub) (main)) :=
  (∃ i, i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length) ↔ result


public theorem len_gt_spec (sub main : List Int) (h : sub.length > main.length) :
    (∃ i, i + sub.length ≤ main.length ∧
          sub = (main.drop i).take sub.length) ↔ False:= by 
sorry


end tmp_lemma_8890