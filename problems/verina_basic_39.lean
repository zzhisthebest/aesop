-- -----Description-----
-- This task requires writing a Lean 4 method that rotates a list of integers to the right by a specified number of positions. The method should produce a new list where each element is shifted to the right while preserving the original list's length.
--
-- -----Input-----
-- The input consists of:
-- • l: A list of integers.
-- • n: A non-negative natural number that indicates the number of positions by which to rotate the list.
--
-- -----Output-----
-- The output is a list of integers:
-- • Returns a list with the same length as the input list, where the elements have been rotated to the right by n positions.
--
-- -----Note-----
-- • The precondition requires that n is non-negative.
-- • If the input list is empty, it should be returned unchanged.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def rotateRight_precond (l : List Int) (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def rotateRight (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) : List Int :=
  -- !benchmark @start code
  let len := l.length
  if len = 0 then l
  else
    (List.range len).map (fun i : Nat =>
      let idx_int : Int := ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
      let idx_nat : Nat := Int.toNat idx_int
      l.getD idx_nat (l.headD 0)
    )
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def rotateRight_postcond (l : List Int) (n : Nat) (result: List Int) (h_precond : rotateRight_precond (l) (n)) :=
  -- !benchmark @start postcond
  result.length = l.length ∧
  (∀ i : Nat, i < l.length →
    let len := l.length
    let rotated_index := Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
    result[i]? = l[rotated_index]?)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem rotateRight_spec_satisfied (l: List Int) (n: Nat) (h_precond : rotateRight_precond (l) (n)) :
    rotateRight_postcond (l) (n) (rotateRight (l) (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
