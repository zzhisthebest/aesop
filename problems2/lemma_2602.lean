import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def maxOfList_precond (lst : List Nat) : Prop :=
  lst.length > 0

def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  let rec helper (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | [x] => x
    | x :: xs =>
      let maxTail := helper xs
      if x > maxTail then x else maxTail

  helper lst

@[reducible, simp]
def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result


theorem if_mem_two (a b : Nat) (h : a > b) :
    (if a > b then a else b) ∈ [a,b]:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp