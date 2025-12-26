-- -----Description----- 
-- This task requires writing a Lean 4 method that solves the Two Sum problem. Given a list of integers and a target integer, the method must return a pair of indices such that the sum of the numbers at those indices equals the target. You may assume that each input has exactly one solution and that you may not use the same element twice. The answer should be returned with first index is smaller than the second.
--
-- -----Input-----
-- The input consists of:
-- - nums: A list of integers.
-- - target: An integer representing the target sum.
--
-- -----Output-----
-- The output is a pair (tuple) of integers representing the indices of the two numbers in the input list that add up to the target.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  let pairwiseSum := List.range nums.length |>.flatMap (fun i =>
    nums.drop (i + 1) |>.map (fun y => nums[i]! + y))
  nums.length > 1 ∧ pairwiseSum.count target = 1
  -- !benchmark @end precond


-- !benchmark @start code_aux
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
-- !benchmark @end code_aux


def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Prod Nat Nat :=
  -- !benchmark @start code
  twoSumAux nums target 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Prod Nat Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  -- !benchmark @start postcond
  let i := result.fst;
  let j := result.snd;
  (i < j) ∧
  (i < nums.length) ∧ (j < nums.length) ∧
  (nums[i]!) + (nums[j]!) = target
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem twoSum_spec_satisfied (nums: List Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



