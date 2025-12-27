-- -----Description-----
-- This task requires writing a Lean 4 method that determines if a given integer is strictly greater than every element in a provided array. The method should return true only if the integer is larger than each element in the array; otherwise, it should return false.
--
-- -----Input-----
-- The input consists of:
-- n: An integer.
-- a: An array of integers.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the integer is greater than all elements in the array.
-- Returns false if there is at least one element in the array that is greater than or equal to the integer.
--
-- -----Note-----
-- The array is assumed to be non-null.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  -- !benchmark @start code
  a.all fun x => n > x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) (h_precond : isGreater_precond (n) (a)) :=
  -- !benchmark @start postcond
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isGreater_spec_satisfied (n: Int) (a: Array Int) (h_precond : isGreater_precond (n) (a)) :
    isGreater_postcond (n) (a) (isGreater (n) (a) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop
  --simp [Array.all_eq]
  -- !benchmark @end proof
--己
