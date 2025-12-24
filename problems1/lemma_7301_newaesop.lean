import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size ≥ 2 ∧

  (List.range nums.size).any (fun i =>
    (List.range i).any (fun j => nums[i]! + nums[j]! = target)) ∧

  ((List.range nums.size).flatMap (fun i =>
    (List.range i).filter (fun j => nums[i]! + nums[j]! = target))).length = 1

def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Array Nat :=
  let rec findIndices (i : Nat) (j : Nat) (fuel : Nat) : Array Nat :=
    match fuel with
    | 0 => #[]
    | fuel+1 =>
      if i >= nums.size then
        #[]
      else if j >= nums.size then
        findIndices (i + 1) (i + 2) fuel
      else
        if nums[i]! + nums[j]! == target then
          #[i, j]
        else
          findIndices i (j + 1) fuel

  findIndices 0 1 (nums.size * nums.size)

@[reducible]
def twoSum_postcond (nums : Array Int) (target : Int) (result: Array Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  result.size = 2 ∧

  result[0]! < nums.size ∧ result[1]! < nums.size ∧

  result[0]! < result[1]! ∧

  nums[result[0]!]! + nums[result[1]!]! = target


theorem twoSum_correct (nums : Array Int) (target : Int)
    (h_precond : twoSum_precond nums target) :
    twoSum_postcond nums target (twoSum nums target h_precond) h_precond:= by 
  aesop?


end tmp