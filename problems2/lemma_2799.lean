import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def maxOfList_precond (lst : List Nat) : Prop :=
  lst ≠ []

def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  let rec helper (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | [x] => x
    | x :: xs =>
      let maxTail := helper xs
      if x > maxTail then x else maxTail
  helper lst

@[reducible]
def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result


theorem mem_cons_cases {α} {x y : α} {xs : List α}
    (h : y ∈ x :: xs) : y = x ∨ y ∈ xs:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp