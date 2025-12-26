-- -----Description----- 
-- This task requires writing a Lean 4 method that identifies the dissimilar elements between two arrays of integers. In other words, the method should return an array containing all elements that appear in one input array but not in the other. The output array must contain no duplicate elements and the order of elements does not matter.
--
-- -----Input-----
-- The input consists of:
-- a: An array of integers.
-- b: An array of integers.
--
-- -----Output-----
-- The output is an array of integers:
-- Returns an array containing all distinct elements from both input arrays that are not present in the other array and should be sorted

-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

-- !benchmark @start solution_aux
def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def dissimilarElements_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- !benchmark @end code_aux


def dissimilarElements (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let res := a.foldl (fun acc x => if !inArray b x then acc.insert x else acc) Std.HashSet.empty
  let res := b.foldl (fun acc x => if !inArray a x then acc.insert x else acc) res
  res.toArray.insertionSort
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def dissimilarElements_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : dissimilarElements_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.all (fun x => inArray a x ≠ inArray b x)∧
  result.toList.Pairwise (· ≤ ·) ∧
  a.all (fun x => if x ∈ b then x ∉ result else x ∈ result) ∧
  b.all (fun x => if x ∈ a then x ∉ result else x ∈ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem dissimilarElements_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    dissimilarElements_postcond (a) (b) (dissimilarElements (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

