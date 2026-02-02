import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  True

def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Option (Nat × Nat) :=
  let rec outer (lst : List Int) (i : Nat)
            : Option (Nat × Nat) :=
        match lst with
        | [] =>
            none
        | x :: xs =>
            let rec inner (lst' : List Int) (j : Nat)
                    : Option Nat :=
                match lst' with
                | [] =>
                    none
                | y :: ys =>
                    if x + y = target then
                        some j
                    else
                        inner ys (j + 1)
            match inner xs (i + 1) with
            | some j =>
                some (i, j)
            | none =>
                outer xs (i + 1)
        outer nums 0

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) : Prop :=
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        List.Pairwise (fun a b => a + b ≠ target) (nums.take i) ∧
        List.all (nums.take i) (fun a => List.all (nums.drop i) (fun b => a + b ≠ target) ) ∧
        List.all (nums.drop (j + 1)) (fun a => a + nums[j]! ≠ target)


theorem outer_index_lt_length (nums : List Int) (i : Nat) (h : i < nums.length) :
    i < (nums.drop i).length + i:= by 
codetic?(config := { enableGrind := false })


end tmp