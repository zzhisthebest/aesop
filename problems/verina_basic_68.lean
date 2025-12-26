-- -----Description-----
-- The task is to determine the position of a target integer in a given array. The goal is to return the index corresponding to the first occurrence of the target value. If the target is not present in the array, the result should indicate that by returning the size of the array. This description focuses entirely on understanding the problem without specifying any particular implementation method.
--
-- -----Input-----
-- The input consists of:
-- • a: An array of integers.
-- • e: An integer representing the target to search for in the array.
--
-- -----Output-----
-- The output is a natural number (Nat) which is:
-- • The index of the first occurrence of the target integer if found.
-- • The size of the array if the target integer is not present.
--
-- -----Note-----
-- There are no strict preconditions on the input; the method should work correctly for any array of integers. The specification ensures that the returned index is always valid: it is either within the array bounds with a matching element or equals the array’s size if the element is absent.

-- !benchmark @start import type=solution
import Lean
namespace tmp
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  True

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0

@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)
open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta
elab "funInduct" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- 查找 LinearSearch.loop 调用
  let some call := goalType.find? (fun e =>
    match e.getAppFn with
    | .const `tmp.LinearSearch.loop _ => true
    | _ => false
  ) | throwError "No LinearSearch.loop call found"

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
    let fixedNames : Array Name := #[name0,name1]  -- 固定参数列表
    let inductNames : Array Name := #[name2]  -- 归纳参数列表
    let inductIdent := mkIdent `LinearSearch.loop.induct

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
theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  unfold LinearSearch_postcond LinearSearch
  constructor
  · --这是一个spec
    --是的，要证明就得数学归纳法，因为0时是最强的，相当于n时
    have aux (x : Nat) : (x ≤ a.size) → LinearSearch.loop a e x ≤ a.size := by
      funInduct
      -- induction x using LinearSearch.loop.induct a e with
      -- | case1 =>
      --   unfold LinearSearch.loop
      --   aesop
      -- | case2 =>
      --   unfold LinearSearch.loop
      --   aesop
      -- | case3 =>
      --   unfold LinearSearch.loop
      --   aesop
      -- intro hx₀ hx₁
      -- let nx := a.size - x
      -- have hn₁ : nx = a.size - x := by rfl
      -- have hn₂ : x = a.size - nx := by
      --   grind
      -- rw [hn₂]
      -- have h1:0<=nx:=by grind
      -- have h2:nx<=a.size:=by grind
      -- clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      -- revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      -- --aesop?
      -- --aesop (config := { useSimpAll := false })
      -- induction nx with
      -- | zero=>
      --   unfold LinearSearch.loop
      --   simp

      -- | succ n1 ih=>
      --   unfold LinearSearch.loop
      --   aesop
    aesop
  · constructor
    · --这是一个spec
      have aux (x : Nat) :  (x ≤ a.size) → LinearSearch.loop a e x = a.size ∨ a[LinearSearch.loop a e x]! = e:= by
        induction x using LinearSearch.loop.induct a e with
        | case1 =>
          unfold LinearSearch.loop
          aesop
        | case2 =>
          unfold LinearSearch.loop
          aesop
        | case3 =>
          unfold LinearSearch.loop
          aesop
        -- intro hx₀ hx₁
        -- let nx := a.size - x
        -- have hn₁ : nx = a.size - x := by rfl
        -- have hn₂ : x = a.size - nx := by
        --   grind
        -- rw [hn₂]
        -- have h1:0<=nx:=by grind
        -- have h2:nx<=a.size:=by grind
        -- clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
        -- revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
        -- induction nx with
        -- | zero=>
        --   unfold LinearSearch.loop
        --   aesop
        -- | succ n1 ih=>
        --   unfold LinearSearch.loop

        --   aesop

      aesop
    · --这是一个spec
      have aux (x : Nat) : (x ≤ a.size) → (∀ i, x ≤ i → i < LinearSearch.loop a e x → a[i]! ≠ e) := by
        induction x using LinearSearch.loop.induct a e with
        | case1 =>
          unfold LinearSearch.loop
          aesop
        | case2 =>
          unfold LinearSearch.loop
          aesop
        | case3 =>
          unfold LinearSearch.loop
          aesop
      --   intro hx₀ hx₁
      --   let nx := a.size - x
      --   have hn₁ : nx = a.size - x := by rfl
      --   have hn₂ : x = a.size - nx := by
      --     grind
      --   rw [hn₂]
      --   have h1:0<=nx:=by grind
      --   have h2:nx<=a.size:=by grind
      --   clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      --   revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      --   induction nx with
      -- | zero=>
      --   unfold LinearSearch.loop
      --   simp
      --   grind

      -- | succ n1 ih=>
      --   unfold LinearSearch.loop
      --   aesop
      aesop

  -- !benchmark @start proof
  -- unfold LinearSearch_postcond LinearSearch
  -- apply And.intro
  -- . let aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → LinearSearch.loop a e x ≤ a.size := by
  --     intro hx₀ hx₁
  --     let nx := a.size - x
  --     have hn₁ : nx = a.size - x := by rfl
  --     have hn₂ : x = a.size - nx := by
  --       rw [hn₁, Nat.sub_sub_self]
  --       apply hx₁
  --     rw [hn₂]
  --     induction nx with
  --     | zero =>
  --       unfold LinearSearch.loop
  --       simp
  --     | succ n₁ ih =>
  --       by_cases hp : (a.size ≤ n₁)
  --       . rw [Nat.sub_eq_zero_of_le hp] at ih
  --         have h_tmp : a.size ≤ n₁ + 1 := Nat.le_add_right_of_le hp
  --         rw [Nat.sub_eq_zero_of_le h_tmp]
  --         exact ih
  --       . have hq : n₁ < a.size := Nat.not_le.mp hp
  --         unfold LinearSearch.loop
  --         simp
  --         split_ifs
  --         . simp
  --         . rw [Nat.sub_add_eq, Nat.sub_add_cancel]
  --           exact ih
  --           apply Nat.zero_lt_sub_of_lt
  --           exact hq
  --         simp
  --   have h₀ : 0 ≤ a.size := by simp
  --   have h_triv : 0 ≤ 0 := by simp
  --   exact aux 0 h_triv h₀
  -- . apply And.intro
  --   . let aux (x : Nat) : (x ≥ 0) → (x ≤ a.size) → LinearSearch.loop a e x = a.size ∨ a[LinearSearch.loop a e x]! = e := by
  --       intro hx₀ hx₁
  --       let nx := a.size - x
  --       have hn₁ : nx = a.size - x := by rfl
  --       have hn₂ : x = a.size - nx := by
  --         rw [hn₁, Nat.sub_sub_self]
  --         apply hx₁
  --       rw [hn₂]
  --       induction nx with
  --       | zero =>
  --         unfold LinearSearch.loop
  --         simp
  --       | succ n₁ ih =>
  --         -- Ohh boy...
  --         by_cases hp : (a.size ≤ n₁)
  --         . rw [Nat.sub_eq_zero_of_le hp] at ih
  --           have h_tmp : a.size ≤ n₁ + 1 := Nat.le_add_right_of_le hp
  --           rw [Nat.sub_eq_zero_of_le h_tmp]
  --           exact ih
  --         . have hq : n₁ < a.size := Nat.not_le.mp hp
  --           apply Or.elim ih -- Didn't find elem, so we're gonna also return a.size...
  --           . intro ih₁
  --             unfold LinearSearch.loop
  --             split_ifs
  --             . rename_i h₁ h₂
  --               rw [h₂]
  --               simp
  --             . rename_i ha₁ ha₂
  --               rw [Nat.sub_add_eq, Nat.sub_add_cancel]
  --               rw [ih₁]
  --               simp
  --               apply Nat.zero_lt_sub_of_lt
  --               exact hq
  --             . rename_i h₁
  --               have ha₁ := Nat.not_lt.mp h₁
  --               have ha₂ := Nat.sub_le a.size (n₁ + 1)
  --               have ha := Nat.eq_iff_le_and_ge.mpr ⟨ha₁, ha₂⟩
  --               rw [←ha]
  --               simp
  --           . intro ih₂
  --             unfold LinearSearch.loop
  --             split_ifs
  --             . rename_i h₁ h₂
  --               rw [h₂]
  --               simp
  --             . rename_i ha₁ ha₂
  --               rw [Nat.sub_add_eq, Nat.sub_add_cancel]
  --               rw [ih₂]
  --               simp
  --               apply Nat.zero_lt_sub_of_lt
  --               exact hq
  --             . rename_i h₁
  --               have ha₁ := Nat.not_lt.mp h₁
  --               have ha₂ := Nat.sub_le a.size (n₁ + 1)
  --               have ha := Nat.eq_iff_le_and_ge.mpr ⟨ha₁, ha₂⟩
  --               rw [←ha]
  --               simp
  --     have h₀ : 0 ≤ 0 := by simp
  --     have h₁ : 0 ≤ a.size := by simp
  --     exact aux 0 h₀ h₁
  --   . let aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → (∀ i, x ≤ i → i < LinearSearch.loop a e x → a[i]! ≠ e) := by
  --       intro hx₀ hx₁ i
  --       let nx := a.size - x
  --       have hn₁ : nx = a.size - x := by rfl
  --       have hn₂ : x = a.size - nx := by
  --         rw [hn₁, Nat.sub_sub_self]
  --         apply hx₁
  --       rw [hn₂]
  --       induction nx with
  --       | zero =>
  --         -- There's no such i
  --         unfold LinearSearch.loop
  --         simp
  --         intro hxi hi
  --         have h_contr := Nat.lt_of_le_of_lt hxi hi
  --         have h : a.size ≤ a.size := by simp
  --         have h : a.size - a.size < a.size - a.size := Nat.sub_lt_sub_right h h_contr
  --         simp at h
  --       | succ n ih =>
  --         intro hxi
  --         unfold LinearSearch.loop
  --         simp
  --         split_ifs
  --         . rename_i h₁ h₂
  --           intro h_contr
  --           have h := Nat.lt_of_le_of_lt hxi h_contr
  --           simp at h
  --         . rename_i h₁ h₂
  --           by_cases hp : (a.size ≤ n)
  --           . rw [Nat.sub_eq_zero_iff_le.mpr hp] at ih
  --             intro hi
  --             have hp₁ : a.size ≤ n + 1 := by
  --               have h₁' : n ≤ n + 1 := by simp
  --               exact Nat.le_trans hp h₁'
  --             rw [Nat.sub_eq_zero_iff_le.mpr hp₁] at hxi
  --             rw [Nat.sub_eq_zero_iff_le.mpr hp₁] at hi
  --             rw [Nat.sub_eq_zero_iff_le.mpr hp₁] at h₂
  --             have ih₁ := ih hxi
  --             simp at hi
  --             unfold LinearSearch.loop at ih₁
  --             split_ifs at ih₁
  --             . rename_i h₁'
  --               simp at ih₁
  --               exact ih₁ hi
  --             . rename_i h₁'
  --               contradiction
  --           . have hq : n < a.size := Nat.not_le.mp hp
  --             have hq' : 1 ≤ a.size - n := by
  --               have h : 0 < a.size - n := by
  --                 exact Nat.sub_pos_of_lt hq
  --               exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt h)
  --             rw [Nat.sub_add_eq, Nat.sub_add_cancel hq']
  --             intro hi
  --             by_cases h_bounds : (a.size - n ≤ i)
  --             . exact ih h_bounds hi
  --             . have h_bounds' : ( i + 1 < a.size - n + 1) := (@Nat.add_lt_add_iff_right 1 i (a.size - n)).mpr (Nat.not_le.mp h_bounds)
  --               have h := Nat.le_of_lt_add_one h_bounds'
  --               apply Nat.le_sub_of_add_le at h
  --               rw [← Nat.sub_add_eq] at h
  --               have hi_fixed := Nat.eq_iff_le_and_ge.mpr ⟨hxi, h⟩
  --               rw [hi_fixed] at h₂
  --               exact h₂
  --         . intro h_contr
  --           have h := Nat.lt_of_le_of_lt hxi h_contr
  --           simp at h
  --     have h₀ : 0 ≤ a.size := by simp
  --     have h_triv : 0 ≤ 0 := by simp
  --     intro i
  --     have h_tmp : 0 ≤ i := Nat.zero_le i
  --     exact aux 0 h_triv h₀ i h_tmp


  -- -- !benchmark @end proof
--己
