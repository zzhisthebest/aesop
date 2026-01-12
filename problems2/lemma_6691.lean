import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def smallestMissing_precond (l : List Nat) : Prop :=
  List.Pairwise (· < ·) l

def smallestMissing (l : List Nat) (h_precond : smallestMissing_precond (l)) : Nat :=
  let sortedList := l
  let rec search (lst : List Nat) (n : Nat) : Nat :=
    match lst with
    | [] => n
    | x :: xs =>
      let isEqual := x = n
      let isGreater := x > n
      let nextCand := n + 1
      if isEqual then
        search xs nextCand
      else if isGreater then
        n
      else
        search xs n
  let result := search sortedList 0
  result

@[reducible]
def smallestMissing_postcond (l : List Nat) (result: Nat) (h_precond : smallestMissing_precond (l)) : Prop :=
  result ∉ l ∧ ∀ candidate : Nat, candidate < result → candidate ∈ l


theorem lt_succ_iff {a b : Nat} : a < b.succ ↔ a = b ∨ a < b:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp