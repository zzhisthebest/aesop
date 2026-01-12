module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_6664
public def smallestMissing_precond (l : List Nat) : Prop :=
  List.Pairwise (· < ·) l

public def smallestMissing (l : List Nat) (h_precond : smallestMissing_precond (l)) : Nat :=
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

public def smallestMissing_postcond (l : List Nat) (result: Nat) (h_precond : smallestMissing_precond (l)) : Prop :=
  result ∉ l ∧ ∀ candidate : Nat, candidate < result → candidate ∈ l


public theorem pairwise_cons_head
    {l : List Nat} (h : List.Pairwise (· < ·) l) :
    ∃ a t, l = a :: t ∧
      (∀ b ∈ t, a < b) ∧ List.Pairwise (· < ·) t:= by 
sorry


end tmp_lemma_6664