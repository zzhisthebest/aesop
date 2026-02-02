import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def removeDuplicates_precond (nums : List Int) : Prop :=
  List.Pairwise (· ≤ ·) nums

def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  match nums with
  | [] =>
    0
  | h :: t =>
    let init := h
    let initCount := 1
    let rec countUniques (prev : Int) (xs : List Int) (k : Nat) : Nat :=
      match xs with
      | [] =>
        k
      | head :: tail =>
        let isDuplicate := head = prev
        if isDuplicate then
          countUniques prev tail k
        else
          let newK := k + 1
          countUniques head tail newK
    countUniques init t initCount

@[reducible]
def removeDuplicates_postcond (nums : List Int) (result: Nat) (h_precond : removeDuplicates_precond (nums)) : Prop :=
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result


theorem sorted_imp_mem_eq_head {a b : Int} {t : List Int}
    (hpair : List.Pairwise (· ≤ ·) (a :: b :: t)) :
    (a ∈ b :: t) → a = b:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp