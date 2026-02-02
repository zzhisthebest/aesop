import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  True

def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
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

@[reducible, simp]
def isSublist_postcond (sub : List Int) (main : List Int) (result: Bool) (h_precond : isSublist_precond (sub) (main)) :=
  (∃ i, i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length) ↔ result


theorem check_step_out_of_range {sub main : List Int} {subLen mainLen i : Nat}
    (hout : i + subLen > mainLen) :
    (if i + subLen > mainLen then false
     else if sub = (main.drop i).take subLen then true
     else if i + 1 ≤ mainLen then false else false) = false:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp