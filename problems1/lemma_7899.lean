import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList

def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : (Nat × Nat) :=
  let n := nums.size
  let rec outer (i : Nat) : Option (Nat × Nat) :=
    if i < n - 1 then
      let rec inner (j : Nat) : Option (Nat × Nat) :=
        if j < n then
          if nums[i]! + nums[j]! = target then
            some (i, j)
          else
            inner (j + 1)
        else
          none
      match inner (i + 1) with
      | some pair => some pair
      | none      => outer (i + 1)
    else
      none
  match outer 0 with
  | some pair => pair
  | none      => panic "twoSum: no solution found"

@[reducible, simp]
def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) :=
  let (i, j) := result
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  List.Pairwise (fun a b => a + b ≠ target) (nums.toList.take i) ∧
  List.all (nums.toList.take i) (fun a => List.all (nums.toList.drop i) (fun b => a + b ≠ target) ) ∧
  List.all (nums.toList.drop (j + 1)) (fun a => a + nums[j]! ≠ target)


theorem inner_index_lt (nums : Array Int) (n i j : Nat) (h : i < n - 1) :
    i + 1 ≤ n:= by 
codetic?(config := { enableGrind := false })


end tmp