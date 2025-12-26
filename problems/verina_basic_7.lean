-- -----Description-----
-- This task requires writing a Lean 4 method that computes the sum of the squares of the first n odd natural numbers. The result should match the formula: (n * (2 * n - 1) * (2 * n + 1)) / 3.
--
-- -----Input-----
-- The input consists of:
-- n: A natural number representing the count of odd natural numbers to consider (n should be non-negative).
--
-- -----Output-----
-- The output is a natural number:
-- Returns the sum of the squares of the first n odd natural numbers, as defined by the formula: (n * (2 * n - 1) * (2 * n + 1)) / 3.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Mathlib
import Tacs.InductionGrind
@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  -- !benchmark @start code
  let rec loop (k : Nat) (sum : Nat) : Nat :=
    if k = 0 then
      sum
    else
      loop (k - 1) (sum + (2 * k - 1) * (2 * k - 1))
  loop n 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :=
  -- !benchmark @start postcond
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux
lemma aux:∀ n x:Nat,sumOfSquaresOfFirstNOddNumbers.loop n x=sumOfSquaresOfFirstNOddNumbers.loop n 0 + x:=by
  intro n x
  induction n generalizing x with
  | zero =>
    unfold sumOfSquaresOfFirstNOddNumbers.loop
    grind
  | succ n ih =>
    unfold sumOfSquaresOfFirstNOddNumbers.loop
    simp
    rw [ih]
    nth_rw 2 [ih]
    grind


theorem sumOfSquaresOfFirstNOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    sumOfSquaresOfFirstNOddNumbers_postcond (n) (sumOfSquaresOfFirstNOddNumbers (n) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold sumOfSquaresOfFirstNOddNumbers sumOfSquaresOfFirstNOddNumbers_postcond
  simp_all
  rw [Nat.sub_eq_zero_iff_le]
  rw [Nat.sub_eq_zero_iff_le]
  -- 将 a ≤ b ∧ b ≤ a 转换为 a = b,
  --因为两个spec本质上是一个spec
  rw [← le_antisymm_iff]
  --现在证明这个spec
  induction n with
  | zero =>
    unfold sumOfSquaresOfFirstNOddNumbers.loop
    simp_all
  | succ n ih=>
    unfold sumOfSquaresOfFirstNOddNumbers.loop
    simp
    rw [aux]
    rw [ih]
    --下面是证明两个多项式相等，和主要思路没啥关系了，是细枝末节
    clear ih
    ring
    -- rw [← Nat.mul_left_inj (by simp : 3 ≠ 0)]
    -- ring
    suffices h1: (n * (n * 2 - 1) + n ^ 2 * (n * 2 - 1) * 2)  + (2 + n * 2 - 1) ^ 2*3 =
      (n * (2 + n * 2 - 1) * 5 + n ^ 2 * (2 + n * 2 - 1) * 2 + (2 + n * 2 - 1) * 3) by
      have h2:(n * (n * 2 - 1) + n ^ 2 * (n * 2 - 1) * 2 + (2 + n * 2 - 1) ^ 2 * 3)/3 =
        (n * (2 + n * 2 - 1) * 5 + n ^ 2 * (2 + n * 2 - 1) * 2 + (2 + n * 2 - 1) * 3)/3:=by
        apply Mathlib.Tactic.LinearCombination.div_eq_const--rw也可以，因为rw也可以是激进的
        exact h1
      clear h1
      rw [←h2]
      clear h2
      nth_rw 2 [Nat.add_div]
      simp
      rw [add_assoc]
      congr
      rw [add_comm]
      simp
      rw [add_comm]
      simp
      grind
      trivial
    rw [add_comm 2 (n*2)]
    simp
    ring
    calc
      _=3 + n * 12 + (n ^2 * 2 - n) + n ^ 2 * 12 + n ^ 2 * (n * 2 - 1) * 2:=by
        rw [Nat.mul_sub]
        ring

      _=3 + n * 12 + (n ^2 * 2 - n) + n ^ 2 * 12 + (n ^ 3 * 4 - n^2 * 2):=by
        rw [Nat.mul_sub]
        ring
        congr
        grind
      _=3 + n * 12 + n ^2 * 2 - n + n ^ 2 * 12 + (n ^ 3 * 4 - n^2 * 2):=by
        congr
        rw [Nat.add_sub_assoc]
        cases n with
          | zero => simp
          | succ n =>
            have h1:(n+1)^2<=(n+1)^2*2:=by grind
            apply le_trans _ h1
            have h2:n+1=(n+1)^1:=by simp
            nth_rw 1 [h2]
            apply Nat.pow_le_pow_right
            simp
            simp
      _=3 + n * 11 + n ^ 2 * 12 + (n ^2 * 2+ (n ^ 3 * 4 - n ^ 2 * 2)):=by
        omega--竟然直接证明了，真省事
      _=3 + n * 11 + n ^ 2 * 12 + n ^ 3 * 4:=by
        congr 1
        rw [←Nat.add_sub_assoc]
        omega
        apply mul_le_mul
        ·  cases n with
          | zero => simp
          | succ n =>
            -- using `apply?`, first result
            gcongr
            all_goals
            simp
            --refine Nat.pow_le_pow_right ?_ ?_ <;> grind
        trivial
        trivial
        positivity








  -- !benchmark @end proof
--己。
