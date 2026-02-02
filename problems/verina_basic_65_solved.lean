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
import Codetic
set_option maxHeartbeats 0
namespace tmp
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
open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta
elab "funInduct" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- #check SquareRoot.boundedLoop.induct
  -- Locate a call to SquareRoot.boundedLoop in the goal
  let some call := goalType.find? (fun e =>
    match e.getAppFn with
    | .const `SquareRoot.boundedLoop _ => true
    | _ => false
  ) | throwError "No SquareRoot.boundedLoop call found"

  let args := call.getAppArgs
  if args.size != 3 then throwError "Expected 3 arguments"

  -- Extract arguments
  let arg0 := args[0]!  -- s_old (fixed parameter)
  let arg1 := args[1]!  -- s (induction parameter)
  let arg2 := args[2]!  -- j (induction parameter)

  if !arg0.isFVar || !arg1.isFVar || !arg2.isFVar then
    throwError "Arguments must be fvars"

  goal.withContext do
    let name0 ← arg0.fvarId!.getUserName
    let name1 ← arg1.fvarId!.getUserName
    let name2 ← arg2.fvarId!.getUserName

    -- Experiment: flexibly handle an arbitrary number of fixed
    -- parameters and induction parameters
    let fixedNames : Array Name := #[name0]          -- list of fixed parameters
    let inductNames : Array Name := #[name1, name2] -- list of induction parameters
    let inductIdent := mkIdent `SquareRoot.boundedLoop.induct

    -- Approach: dynamically construct and parse a tactic string
    -- (most flexible, can handle arbitrary arity)
    let inductStr := String.intercalate ", " (inductNames.map toString).toList
    let fixedStr := String.intercalate " " (fixedNames.map toString).toList
    let tacticStr := s!"induction {inductStr} using {inductIdent.getId} {fixedStr}"

    -- Parse the tactic string using the tactic parser
    let env ← getEnv
    let parserFn := Parser.runParserCategory env `tactic tacticStr
    match parserFn with
    | Except.ok stx => evalTactic stx
    | Except.error err => throwError "Failed to parse tactic: {err}"

#check SquareRoot.boundedLoop

--又是这种.induct归约
theorem SquareRoot_spec_satisfied (N: Nat) (h_precond : SquareRoot_precond (N)) :
    SquareRoot_postcond (N) (SquareRoot (N) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold SquareRoot_postcond SquareRoot
  constructor
  -- · --这是一个spec
  --   let n_start := 0
  --   suffices r_le : n_start * n_start ≤ N →
  --     (SquareRoot.boundedLoop N (N + 1) n_start) * (SquareRoot.boundedLoop N (N + 1) n_start) ≤ N by
  --     codetic

  --   induction N+1 , n_start using SquareRoot.boundedLoop.induct N with
  --   | case1 r =>
  --     --unfold SquareRoot.boundedLoop
  --     codetic
  --     --codetic?
  --   | case2 bound r h_cond ih =>
  --     codetic
  --   | case3 bound r h_not_cond =>
  --     codetic
  sorry


  · --这是一个spec
    -- 这里用 suffices 构造一个带步数约束的 motive
    suffices h :forall n_start:Nat, (N - n_start < N + 1) → N < (SquareRoot.boundedLoop N (N + 1) n_start + 1)^2 by
      codetic

    -- #check fun (zzh : Nat) => SquareRoot.boundedLoop.induct zzh _ -- 假设命题类型是 Prop
    -- _ _ _                       -- 跳过 case1, case2, case3 的具体证明
    -- (zzh + 1)                   -- 填入 bound 的起点
    -- 0
    intro n_start
    simp_all only [SquareRoot_precond]
    codetic (add unsafe 99% (by revert a))
    --sorry
    --从这里可以看出来不能限制为变量，N+1并不是变量
    induction N + 1, n_start using tmp.SquareRoot.boundedLoop.induct N with
    | case1 r =>
      unfold SquareRoot.boundedLoop
      codetic
    | case2 b r h_cond ih =>
      unfold SquareRoot.boundedLoop
      codetic
    | case3 b r h_not_cond =>
      unfold SquareRoot.boundedLoop
      codetic
  -- !benchmark @end proof

end tmp
