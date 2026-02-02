import Codetic
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


theorem helper_cons_spec (h m : Nat) (xs : List Nat)
    (hm : m ∈ xs ∧ ∀ x ∈ xs, x ≤ m) :
    (if h > m then h else m) ∈ h :: xs ∧
    ∀ x ∈ h :: xs, x ≤ (if h > m then h else m):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp