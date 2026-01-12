import Aesop
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


theorem removeDuplicates_cons_eq (a : Int) (t : List Int)
    (h : List.Pairwise (· ≤ ·) (a :: t)) :
    removeDuplicates (a :: t) h =
      (if a ∈ t then
          removeDuplicates t ((List.pairwise_cons.1 h).2)
        else
          (removeDuplicates t ((List.pairwise_cons.1 h).2)) + 1):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp