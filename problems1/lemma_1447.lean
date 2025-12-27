import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  True

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Int :=
  let rec lisHelper (dp : List Int) (x : Int) : List Int :=
    let rec replace (l : List Int) (acc : List Int) : List Int :=
      match l with
      | [] => (acc.reverse ++ [x])
      | y :: ys => if x ≤ y then acc.reverse ++ (x :: ys) else replace ys (y :: acc)
    replace dp []

  let finalDP := nums.foldl lisHelper []
  finalDP.length

@[reducible, simp]
def lengthOfLIS_postcond (nums : List Int) (result: Int) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  let rec isStrictlyIncreasing (l : List Int) : Bool :=
    match l with
    | [] | [_] => true
    | x :: y :: rest => x < y && isStrictlyIncreasing (y :: rest)

  let rec subsequences (xs : List Int) : List (List Int) :=
    match xs with
    | [] => [[]]
    | x :: xs' =>
      let rest := subsequences xs'
      rest ++ rest.map (fun r => x :: r)

  let allIncreasing := subsequences nums |>.filter (fun l => isStrictlyIncreasing l)

  allIncreasing.any (fun l => l.length = result) ∧
  allIncreasing.all (fun l => l.length ≤ result)


theorem filter_preserves_membership (xs : List (List Int)) (p : List Int → Bool) :
  (xs.filter p).length ≤ xs.length:= by 
aesop


end tmp