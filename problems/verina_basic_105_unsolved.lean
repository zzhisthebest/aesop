-- -----Description-----
-- This task involves computing the element-wise product of two integer arrays. For each position in the arrays, the corresponding numbers are multiplied together. If an element is missing in one of the arrays at a given index, the missing value is treated as 0. When both arrays provide values for every index, the resulting array will contain the product of the two numbers at each corresponding index.
--
-- -----Input-----
-- The input consists of two arrays:
-- • a: An array of integers.
-- • b: An array of integers (should be of equal length to a for the specification to hold).
--
-- -----Output-----
-- The output is an array of integers that:
-- • Has the same length as the input arrays.
-- • For each index i, the output array contains the product a[i] * b[i].
-- • In cases where one of the arrays might be shorter, missing elements default to 0 during multiplication.
--
-- -----Note-----
-- It is assumed that the arrays are of equal length for the theorem specification, although the implementation defaults missing indices to 0.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
import Aesop
namespace tmp
-- !benchmark @end precond_aux
@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size
  -- !benchmark @end precond


-- !benchmark @start code_aux
def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c
-- !benchmark @end code_aux


def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let len := a.size
  let c := Array.mkArray len 0
  loop a b len 0 c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayProduct_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem arrayProduct_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    arrayProduct_postcond (a) (b) (arrayProduct (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop
  -- !benchmark @end proof
