-- -----Description-----
-- This task involves computing the integer square root of a given natural number. The goal is to determine the largest natural number r that satisfies r * r ≤ N and N < (r + 1) * (r + 1).
--
-- -----Input-----
-- The input consists of:
-- • N: A natural number.
--
-- -----Output-----
-- The output is a natural number r that meets the following conditions:
-- • r * r ≤ N
-- • N < (r + 1) * (r + 1)
--
-- -----Note-----
-- The implementation relies on a recursive strategy to iteratively increment r until (r + 1)*(r + 1) exceeds N. Edge cases, such as N = 0, should be handled correctly.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop

@[reducible, simp]
def SquareRoot_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  -- !benchmark @start code
  let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r--这个分支永远不会运行到
    | bound+1, r =>
        if (r + 1) * (r + 1) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SquareRoot_postcond (N : Nat) (result: Nat) (h_precond : SquareRoot_precond (N)) :=
  -- !benchmark @start postcond
  result * result ≤ N ∧ N < (result + 1) * (result + 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

--又是这种.induct归约
theorem SquareRoot_spec_satisfied (N: Nat) (h_precond : SquareRoot_precond (N)) :
    SquareRoot_postcond (N) (SquareRoot (N) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold SquareRoot_postcond SquareRoot
  constructor
  · --这是一个spec
    let n_start := 0
    suffices r_le : n_start * n_start ≤ N →
      (SquareRoot.boundedLoop N (N + 1) n_start) * (SquareRoot.boundedLoop N (N + 1) n_start) ≤ N by
      aesop

    induction N+1 , n_start using SquareRoot.boundedLoop.induct N with
    | case1 r =>
      --unfold SquareRoot.boundedLoop
      aesop
      --aesop?
    | case2 bound r h_cond ih =>
      aesop
    | case3 bound r h_not_cond =>
      aesop


  · --这是一个spec
    let n_start := 0
    -- 这里用 suffices 构造一个带步数约束的 motive
    suffices h : (N - n_start < N + 1) → N < (SquareRoot.boundedLoop N (N + 1) n_start + 1)^2 by
      aesop

    -- #check fun (zzh : Nat) => SquareRoot.boundedLoop.induct zzh _ -- 假设命题类型是 Prop
    -- _ _ _                       -- 跳过 case1, case2, case3 的具体证明
    -- (zzh + 1)                   -- 填入 bound 的起点
    -- 0
    induction N + 1, n_start using SquareRoot.boundedLoop.induct N with
    | case1 r =>
      aesop
    | case2 b r h_cond ih =>
      unfold SquareRoot.boundedLoop
      aesop
    | case3 b r h_not_cond =>
      aesop
  -- !benchmark @end proof

--
