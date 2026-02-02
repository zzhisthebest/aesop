-- -----Description-----
-- This task involves determining how many numbers within an array are less than a specified threshold. The problem is focused on identifying and counting such numbers based purely on their value in relation to the threshold.
--
-- -----Input-----
-- The input consists of:
-- • numbers: An array of integers (which may be empty or non-empty).
-- • threshold: An integer that serves as the comparison threshold.
--
-- -----Output-----
-- The output is a natural number (Nat) representing the count of elements in the array that are less than the given threshold.
--
-- -----Note-----
-- There are no additional preconditions; the function should work correctly for any array of integers and any integer threshold.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
import Codetic
namespace tmp
-- !benchmark @end precond_aux
@[reducible, simp]
def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0
-- !benchmark @end code_aux


def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  -- !benchmark @start code
  countLessThan numbers threshold
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  -- !benchmark @start postcond
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem CountLessThan_spec_satisfied (numbers: Array Int) (threshold: Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    CountLessThan_postcond (numbers) (threshold) (CountLessThan (numbers) (threshold) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  sorry
  -- !benchmark @end proof
