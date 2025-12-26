-- -----Description-----
-- Given a sequence of n integers, your task is to find the largest sum obtainable by choosing a contiguous subarray of the sequence. At least one number must be selected.
--
-- The algorithm uses dynamic programming (Kadane’s Algorithm) to solve the problem:
-- 1. Initialize the current maximum (cur) and the overall maximum (maxSoFar) with the first element.
-- 2. For each subsequent element, update:
--      cur = max(element, cur + element)
--      maxSoFar = max(maxSoFar, cur)
-- 3. Return maxSoFar as the answer.
--
-- -----Input-----
-- The input is provided as a list of integers:
--   sequence: A list of n integers.
--
-- -----Output-----
-- The output is a single integer representing the maximum subarray sum.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def task_code_precond (sequence : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def task_code (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  -- !benchmark @start code
  match sequence with
  | []      => 0  -- If no elements are provided (should not happen according to the problem)
  | x :: xs =>
      let (_, maxSoFar) :=
        xs.foldl (fun (acc : Int × Int) (x : Int) =>
          let (cur, maxSoFar) := acc
          let newCur := if cur + x >= x then cur + x else x
          let newMax := if maxSoFar >= newCur then maxSoFar else newCur
          (newCur, newMax)
        ) (x, x)
      maxSoFar
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def task_code_postcond (sequence : List Int) (result: Int) (h_precond : task_code_precond (sequence)) : Prop :=
  -- !benchmark @start postcond
  let subArrays :=
    List.range (sequence.length + 1) |>.flatMap (fun start =>
      List.range (sequence.length - start + 1) |>.map (fun len =>
        sequence.drop start |>.take len))
  let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum)
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem task_code_spec_satisfied (sequence: List Int) (h_precond : task_code_precond (sequence)) :
    task_code_postcond (sequence) (task_code (sequence) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof



