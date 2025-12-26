-- -----Description-----
-- This task requires writing a Lean 4 function that finds the majority element in a list of integers. The majority element is the element that appears more than ⌊n/2⌋ times, where n is the list’s length. You may assume that a majority element always exists in the input.
--
-- -----Input-----
-- - nums: A list of integers of length ≥ 1, containing a majority element.
--
-- -----Output-----
-- - An integer: the element that appears more than ⌊n/2⌋ times.
--
--

-- !benchmark @start import type=solution
import Std.Data.HashMap
open Std
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def majorityElement_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  -- !benchmark @start code
  Id.run do
    let mut counts : HashMap Int Nat := {}
    let n := nums.length
    for x in nums do
      let count := counts.getD x 0
      counts := counts.insert x (count + 1)
    match counts.toList.find? (fun (_, c) => c > n / 2) with
    | some (k, _) => k
    | none      => 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  (nums.count result) > n / 2
  ∧ ∀ x, x ≠ result → nums.count x ≤ n / 2
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem majorityElement_spec_satisfied (nums: List Int) (h_precond : majorityElement_precond (nums)) :
    majorityElement_postcond (nums) (majorityElement (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



