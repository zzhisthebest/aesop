import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  let pairwiseSum := List.range nums.length |>.flatMap (fun i =>
    nums.drop (i + 1) |>.map (fun y => nums[i]! + y))
  nums.length > 1 ∧ pairwiseSum.count target = 1

def findComplement (nums : List Int) (target : Int) (i : Nat) (x : Int) : Option Nat :=
  let rec aux (nums : List Int) (j : Nat) : Option Nat :=
    match nums with
    | []      => none
    | y :: ys => if x + y = target then some (i + j + 1) else aux ys (j + 1)
  aux nums 0

def twoSumAux (nums : List Int) (target : Int) (i : Nat) : Prod Nat Nat :=
  match nums with
  | []      => panic! "No solution exists"
  | x :: xs =>
    match findComplement xs target i x with
    | some j => (i, j)
    | none   => twoSumAux xs target (i + 1)

def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Prod Nat Nat :=
  twoSumAux nums target 0

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Prod Nat Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  let i := result.fst;
  let j := result.snd;
  (i < j) ∧
  (i < nums.length) ∧ (j < nums.length) ∧
  (nums[i]!) + (nums[j]!) = target


theorem findComplement_eq_some_iff (nums : List Int) (target : Int) (i : Nat) (x : Int) (j : Nat) :
    findComplement nums target i x = some j ↔
      ∃ k, k < nums.length ∧ x + nums[k]! = target ∧ j = i + k + 1:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp