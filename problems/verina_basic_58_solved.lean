-- -----Description-----
-- This task involves transforming an array of integers by doubling each element.
--
-- -----Input-----
-- The input consists of:
-- • s: An array of integers.
--
-- -----Output-----
-- The output is an array of integers where for each valid index i, the element at position i is equal to twice the corresponding element in the input array.
--
-- -----Note-----
-- The implementation makes use of a recursive helper function to update the array in place. It is assumed that the input array is valid and that the doubling operation does not lead to any overflow issues.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
--import Aesop
import Lean
import Aesop
namespace tmp
@[reducible, simp]
def double_array_elements_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s
termination_by s.size - i
-- !benchmark @end code_aux


def double_array_elements (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  -- !benchmark @start code
  double_array_elements_aux s s 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def double_array_elements_postcond (s : Array Int) (result: Array Int) (h_precond : double_array_elements_precond (s)) :=
  -- !benchmark @start postcond
  result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux
open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta
elab "funInduct" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  --#check tmp.double_array_elements_aux.induct
  -- 查找 double_array_elements_aux 调用
  let some call := goalType.find? (fun e =>
    match e.getAppFn with
    | .const `tmp.double_array_elements_aux _ => true
    | _ => false
  ) | throwError "No double_array_elements_aux call found"

  let args := call.getAppArgs
  if args.size != 3 then throwError "Expected 3 arguments"

  -- 获取参数名
  let arg0 := args[0]!  -- s_old (固定)
  let arg1 := args[1]!  -- s (归纳)
  let arg2 := args[2]!  -- j (归纳)

  if !arg0.isFVar || !arg1.isFVar || !arg2.isFVar then
    throwError "Arguments must be fvars"

  goal.withContext do
    let name0 ← arg0.fvarId!.getUserName
    let name1 ← arg1.fvarId!.getUserName
    let name2 ← arg2.fvarId!.getUserName

    -- 实验：灵活处理任意个数的固定参数和归纳参数
    let fixedNames : Array Name := #[name0]  -- 固定参数列表
    let inductNames : Array Name := #[name1, name2]  -- 归纳参数列表
    let inductIdent := mkIdent `tmp.double_array_elements_aux.induct

    -- 方法：动态解析字符串（最灵活，可处理任意个数）
    let inductStr := String.intercalate ", " (inductNames.map toString).toList
    let fixedStr := String.intercalate " " (fixedNames.map toString).toList
    let tacticStr := s!"induction {inductStr} using {inductIdent.getId} {fixedStr}"

    -- 使用 Parser 解析 tactic 字符串
    let env ← getEnv
    let parserFn := Parser.runParserCategory env `tactic tacticStr
    match parserFn with
    | Except.ok stx => evalTactic stx
    | Except.error err => throwError "Failed to parse tactic: {err}"

-- attribute [aesop safe constructors cases] Array
#check tmp.double_array_elements_aux.induct
theorem double_array_elements_spec_satisfied (s: Array Int) (h_precond : double_array_elements_precond (s)) :
    double_array_elements_postcond (s) (double_array_elements (s) h_precond) h_precond := by
  -- !benchmark @start proof
  simp_all only [double_array_elements_postcond, double_array_elements, getElem!_pos]
  simp_all only [double_array_elements_precond]
  --obtain ⟨d⟩ := s
  --simp_all only [List.size_toArray, List.getElem_toArray]
  apply And.intro
  · --这是一个spec
    have aux : ∀ (s_old s : Array Int) (i : Nat),
    s.size = s_old.size → (double_array_elements_aux s_old s i).size = s_old.size := by
      intro s_old s i
      aesop
      -- induction s,i using double_array_elements_aux.induct s_old  with
      -- | case1 s i h new_s ih=>
      --   -- 递归分支：i < s.size
      --   unfold double_array_elements_aux
      --   aesop
      -- | case2 s_old s i  =>
      --   unfold double_array_elements_aux
      --   aesop
    sorry
    --aesop
    --rw [size_eq_length]
    --aesop
    --aesop
  · intro i a
    --sorry
    have aux : ∀ (s_old s : Array Int) (j : Nat),
    s.size = s_old.size →
    (∀ k < s_old.size, s[k]! = if k < j then 2 * s_old[k]! else s_old[k]!) →
    (double_array_elements_aux s_old s j)[i]! = 2 * s_old[i]! := by
      intro s_old s j h1 h2
      --funInduct
      aesop

      -- induction s,j using double_array_elements_aux.induct s_old  with
      -- | case1 s_old i h new_s ih=>
      --   unfold double_array_elements_aux
      --   aesop
      --   --aesop
      -- | case2 s_old s i  =>
      --   unfold double_array_elements_aux
      --   rename_i s_1 i_1 s_old_1
      --   simp_all only [Nat.not_lt, getElem!_pos, Array.set!_eq_setIfInBounds, getElem!_neg, Int.default_eq_zero,
      --     Int.mul_comm, Int.zero_mul]
      --   simp_all only
      --   obtain ⟨toList⟩ := s_1
      --   obtain ⟨toList_1⟩ := s_old_1
      --   obtain ⟨toList_2⟩ := s_old
      --   simp_all only [List.size_toArray, List.getElem_toArray, List.setIfInBounds_toArray, List.getElem!_toArray,
      --     List.getElem!_eq_getElem?_getD, Int.default_eq_zero]
      --   split
      --   next h => grind
      --   next
      --     h =>
      --     simp_all only [Nat.not_lt, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, Int.default_eq_zero]
      --     grind

    -- aesop?


  -- !benchmark @end proof
end tmp
