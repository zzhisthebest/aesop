-- -----Description-----
-- This task requires writing a Lean 4 method that returns the k most frequent elements from a list of integers. The method should count the frequency of each distinct element in the list and return the k elements with the highest frequency.
--
-- -----Input-----
-- The input consists of two values:
-- nums: A list of integers, possibly with duplicates.
-- k: A natural number indicating how many of the most frequent elements to return. Assimng k <= # of distinct elements in nums. 
--
-- -----Output-----
-- The output is a list of integers:
-- Returns exactly k integers representing the elements that appear most frequently in the input list in the order form the higher frequency to lower frequency.
-- If two numbers have the same frequency, use the order of the first occurance in nums.
--

-- !benchmark @start import type=solution
import Std
open Std
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≤ nums.eraseDups.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def topKFrequent (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) : List Int :=
  -- !benchmark @start code
  let freqMap : HashMap Int Nat :=
    nums.foldl (init := {}) fun acc n =>
      let oldVal := match acc.toList.find? (fun (key, _) => key == n) with
                    | some (_, c) => c
                    | none        => 0
      acc.insert n (oldVal + 1)
  let sorted := freqMap.toList.foldl
    (fun acc pair =>
      let (x, cx) := pair
      let rec insertSorted (xs : List (Int × Nat)) : List (Int × Nat) :=
        match xs with
        | [] => [pair]
        | (y, cy) :: ys =>
          if cx > cy then
            pair :: (y, cy) :: ys
          else
            (y, cy) :: insertSorted ys
      insertSorted acc
    ) []

  sorted.take k |>.map (fun (n, _) => n)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) (h_precond : topKFrequent_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  -- Result contains exactly k elements
  result.length = k ∧

  -- All elements in result appear in the original list
  result.all (· ∈ nums) ∧

  -- All elements in result are distinct
  List.Pairwise (· ≠ ·) result ∧

  -- For any element in result and any element not in result, the frequency of the
  -- element in result is greater or equal
  (result.all (fun x =>
    nums.all (fun y =>
      y ∉ result →
        nums.count x > nums.count y ∨
        (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
    ))) ∧

  -- Elements in result are ordered by decreasing frequency
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x > nums.count y ∨
    (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
  ) result.zipIdx
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem topKFrequent_spec_satisfied (nums: List Int) (k: Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    topKFrequent_postcond (nums) (k) (topKFrequent (nums) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



