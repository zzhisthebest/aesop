module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_2413
public def majorityElement_precond (nums : List Int) : Prop :=
  True

public def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  let rec insert (x : Int) (xs : List Int) : List Int :=
    match xs with
    | [] => [x]
    | h :: t =>
      if x ≤ h then
        x :: h :: t
      else
        h :: insert x t

  let rec insertionSort (xs : List Int) : List Int :=
    match xs with
    | [] => []
    | h :: t =>
      let sortedTail := insertionSort t
      let sorted := insert h sortedTail
      sorted

  let getAt := fun (xs : List Int) (i : Nat) =>
    match xs.drop i with
    | [] => 0
    | h :: _ => h

  let sorted := insertionSort nums

  let len := sorted.length
  let mid := len / 2
  getAt sorted mid

public def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  let n := nums.length
  (List.count result nums > n / 2) ∧
  nums.all (fun x => x = result ∨ List.count x nums ≤ n / 2)


public theorem mid_lt_length (xs : List Int) (h : xs ≠ []) :
    xs.length / 2 < xs.length:= by 
sorry


end tmp_lemma_2413