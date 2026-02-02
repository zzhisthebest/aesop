-- -----Description-----
-- The task is to compute the element-wise sum of two integer arrays. The result should be a new array where each element is the sum of the corresponding elements from the two input arrays. The problem assumes that both arrays have the same length.
--
-- -----Input-----
-- The input consists of two parameters:
-- • a: An array of integers.
-- • b: An array of integers.
-- Note: Both arrays must have the same length.
--
-- -----Output-----
-- The output is an array of integers that:
-- • Has the same size as the input arrays.
-- • Contains elements where each element at index i is computed as a[i]! + b[i]! from the input arrays.
--
-- -----Note-----
-- It is assumed that the two input arrays have equal lengths.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
import Codetic
namespace tmp
-- !benchmark @end precond_aux
@[reducible, simp]
def arraySum_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def arraySum (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  if a.size ≠ b.size then
    panic! "Array lengths mismatch"
  else
    let n := a.size;
    let c := Array.mkArray n 0;
    let rec loop (i : Nat) (c : Array Int) : Array Int :=
      if i < n then
        let c' := c.set! i (a[i]! + b[i]!);
        loop (i + 1) c'
      else c;
    loop 0 c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def arraySum_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arraySum_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → a[i]! + b[i]! = result[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem arraySum_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arraySum_precond (a) (b)) :
    arraySum_postcond (a) (b) (arraySum (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  codetic
  -- !benchmark @end proof
