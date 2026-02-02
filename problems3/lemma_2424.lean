import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def majorityElement_precond (nums : List Int) : Prop :=
  True

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
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

@[reducible, simp]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  let n := nums.length
  (List.count result nums > n / 2) ∧
  nums.all (fun x => x = result ∨ List.count x nums ≤ n / 2)


theorem getAt_eq (xs : List Int) (i : Nat) :
    (by
      let getAt := fun (ys : List Int) (j : Nat) =>
        match ys.drop j with
        | [] => 0
        | h :: _ => h
      exact getAt xs i = (xs.drop i).headD 0):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp