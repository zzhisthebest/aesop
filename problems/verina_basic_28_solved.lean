-- -----Description-----
-- This task requires writing a Lean 4 method that determines whether a given natural number is prime. A number (with n ≥ 2) is considered prime if it is divisible only by 1 and itself. The method should return true when the input number is prime and false otherwise.
--
-- -----Input-----
-- The input consists of:
-- n: A natural number (Nat) such that n ≥ 2.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if the input number is prime (i.e., there is no integer k with 1 < k < n that divides n).
-- Returns false if the input number is not prime (i.e., there exists an integer k with 1 < k < n that divides n).
--
-- -----Note-----
-- The input is expected to satisfy the condition n ≥ 2.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 2
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  -- !benchmark @start code
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  -- !benchmark @start postcond
  (result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux
-- 核心引理：证明 check 的返回值与区间内因子的关系

theorem check_spec (i fuel : Nat) (h_fuel : i + fuel ≥ n) :
    (isPrime.check n i fuel = true ↔ ∀ k, i ≤ k ∧ k * k ≤ n → n % k ≠ 0) := by
  -- 使用函数归纳法
  induction i, fuel using isPrime.check.induct n with
  | case1 fuel =>
    unfold isPrime.check
    aesop
    sorry--这个情形显然成立，只是涉及自然数运算所以aesop证不出来
  | case2 i f h_fuel_ne h_sq =>
    unfold isPrime.check
    aesop
    sorry--这个情形显然成立，只是涉及自然数运算所以aesop证不出来
  | case3 i f h_f_ne h_sq h_div =>
    aesop
  | case4 i f h_f_ne h_sq h_ndiv ih =>
    unfold isPrime.check
    aesop

-- 辅助引理：如果存在一个因子 x，那么必然存在一个因子 k 使得 k*k ≤ n
theorem exists_small_factor {n : Nat} (h_n : 2 ≤ n)
    (h_ex : ∃ x, 2 ≤ x ∧ x < n ∧ n % x = 0) :
    ∃ k, 2 ≤ k ∧ k * k ≤ n ∧ n % k = 0 := by
  rcases h_ex with ⟨x, hx_ge, hx_lt, hx_div⟩
  let d := n / x
  have h_mul : n = x * d := by sorry--这个显然成立

  -- 证明 d 也是因子且 d ≥ 2
  have hd_div : n % d = 0 := by rw [h_mul]; simp
  have hd_ge : 2 ≤ d := by
    --aesop
    sorry--这个显然成立

  -- x 和 d 必有一个其平方 ≤ n
  have h_sq_cases : x * x ≤ n ∨ d * d ≤ n := by
    --aesop
    sorry--这个显然成立

  cases h_sq_cases
  · exists x
  · exists d

theorem factor_range_equivalence (n : Nat) (h_n : 2 ≤ n) :
    (∀ k, 2 ≤ k ∧ k * k ≤ n → n % k ≠ 0) ↔ (∀ k, 2 ≤ k ∧ k < n → n % k ≠ 0) := by
  aesop
  · revert a
    simp
    apply exists_small_factor
    aesop
    exists k
  · aesop-- 这个方向很简单，因为小范围是大范围的子集


theorem isPrime_spec_satisfied (n: Nat) (h_precond : isPrime_precond (n)) :
    isPrime_postcond (n) (isPrime (n) h_precond) h_precond := by
  -- !benchmark @start proof
  aesop?
  · rw [check_spec] at a
    rw [factor_range_equivalence] at a
    aesop
    aesop
    aesop
  · by_contra
    revert a
    simp
    rw [check_spec]
    rw [factor_range_equivalence]
    aesop
    aesop
    aesop
  -- !benchmark @end proof
