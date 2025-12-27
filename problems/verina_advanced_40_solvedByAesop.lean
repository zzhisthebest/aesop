-- -----Description-----
-- This task requires writing a Lean 4 function that returns the maximum element from a non-empty list of natural numbers.
--
-- -----Input-----
-- The input consists of:
-- lst: a non-empty list of natural numbers.
--
-- -----Output-----
-- The output is:
-- A natural number representing the largest element in the list.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
import Aesop
namespace tmp
-- !benchmark @end precond_aux
@[reducible]
def maxOfList_precond (lst : List Nat) : Prop :=
  -- !benchmark @start precond
  lst ≠ []  -- Ensure the list is non-empty
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  -- !benchmark @start code
  let rec helper (lst : List Nat) : Nat :=
    match lst with
    | [] => 0  -- technically shouldn't happen if input is always non-empty
    | [x] => x
    | x :: xs =>
      let maxTail := helper xs
      if x > maxTail then x else maxTail
  helper lst
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxOfList_spec_satisfied (lst: List Nat) (h_precond : maxOfList_precond (lst)) :
    maxOfList_postcond (lst) (maxOfList (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop
  unfold maxOfList maxOfList_postcond
  constructor
  · induction lst with
    | nil =>
      contradiction
    | cons x xs ih =>
      -- rw [maxOfList.helper]--这里rw不是等价变换，而是激进的，就像要证明a<=b,rw之后变成了证明a<b,因为它排除了| [x] => x分支，而实际上不应该排除，所以不能这么写，要先by_cases
      by_cases ¬xs=[]
      · rw [maxOfList.helper]
        split
        simp
        simp
        · by_cases h1:maxOfList.helper xs = x
          · left
            assumption
          · right
            apply ih
            simp_all
        · simp_all
      · simp_all
        rw [maxOfList.helper]--这次匹配到了| [x] => x分支
  · induction lst with
    | nil =>
      simp
    | cons x xs ih =>
      by_cases ¬xs=[]
      · rw [maxOfList.helper]
        · intro x1 h1
          split
          · simp_all
            cases h1
            · omega
            · have h1:x1≤ maxOfList.helper xs:=by
                apply ih
                assumption
              apply Nat.le_trans h1
              omega
          · rename_i h2
            simp at h2
            by_cases x1=x
            · rename_i h3
              rw [h3]
              assumption
            · simp_all--这个simp_all让我少写了很多繁琐步骤

        · simp_all
      · simp_all
        rw [maxOfList.helper]--这次匹配到了| [x] => x分支
        simp

  -- !benchmark @end proof
