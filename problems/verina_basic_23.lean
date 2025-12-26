-- -----Description-----
-- This task requires writing a Lean 4 method that calculates the difference between the maximum and minimum values in an array of integers. In other words, the method should determine the highest and lowest numbers in the array and return the result of subtracting the minimum from the maximum.
--
-- -----Input-----
-- The input consists of:
-- a: An array of integers.
--
-- -----Output-----
-- The output is an integer:
-- Returns the difference between the largest and the smallest values in the input array.
--
-- -----Note-----
-- The input array is assumed to be non-empty.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def differenceMinMax_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def differenceMinMax (a : Array Int) (h_precond : differenceMinMax_precond (a)) : Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (minVal maxVal : Int) : Int :=
    if i < a.size then
      let x := a[i]!
      let newMin := if x < minVal then x else minVal
      let newMax := if x > maxVal then x else maxVal
      loop (i + 1) newMin newMax
    else
      maxVal - minVal
  loop 1 (a[0]!) (a[0]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def differenceMinMax_postcond (a : Array Int) (result: Int) (h_precond : differenceMinMax_precond (a)) :=
  -- !benchmark @start postcond
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem differenceMinMax_spec_satisfied (a: Array Int) (h_precond : differenceMinMax_precond (a)) :
    differenceMinMax_postcond (a) (differenceMinMax (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold differenceMinMax_postcond differenceMinMax
  simp

  sorry
  -- !benchmark @end proof
