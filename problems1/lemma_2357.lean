import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def majorityElement_precond (xs : List Nat) : Prop :=
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)

def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  let rec countOccurrences (target : Nat) (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | y :: ys =>
      if y = target then 1 + countOccurrences target ys
      else countOccurrences target ys

  let rec findCandidate (lst : List Nat) (candidate : Option Nat) (count : Nat) : Nat :=
    match lst with
    | [] =>
      match candidate with
      | some c => c
      | none => 0
    | x :: xs =>
      match candidate with
      | some c =>
        if x = c then
          findCandidate xs (some c) (count + 1)
        else if count = 0 then
          findCandidate xs (some x) 1
        else
          findCandidate xs (some c) (count - 1)
      | none =>
        findCandidate xs (some x) 1

  let cand := findCandidate xs none 0
  cand

@[reducible]
def majorityElement_postcond (xs : List Nat) (result: Nat) (h_precond : majorityElement_precond (xs)) : Prop :=
  let count := xs.count result
  count > xs.length / 2


theorem count_gt_half_unique {xs : List Nat} {a b : Nat}
    (ha : xs.count a > xs.length / 2) (hb : xs.count b > xs.length / 2) :
    a = b:= by 
aesop


end tmp