-- -----Description-----
-- This task requires writing a Lean 4 function that finds the single number in a non-empty list of integers, where every element appears exactly twice except for one element that appears only once. The function
-- should return the integer that appears only once.
--
-- -----Input-----
-- The input is a non-empty list of integers:
-- - nums: A list in which each integer appears exactly twice except for one element that appears only once.
--
-- -----Output-----
-- The output is a single integer:
-- Returns the unique integer that appears exactly once in the list.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
import Codetic
--返回nums中等于x的元素的列表
def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
--nums中每个元素出现次数为1或2，且只有一个元素出现次数为1
@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- !benchmark @end code_aux


def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  -- !benchmark @start code
  let rec findUnique (remaining : List Int) : Int :=
    match remaining with
    | [] =>--这个分支永远不可能执行
      0
    | x :: xs =>
      let filtered : List Int :=
        filterlist x nums
      let count : Nat :=
        filtered.length
      if count = 1 then
        x
      else
        findUnique xs
  findUnique nums
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def FindSingleNumber_postcond (nums : List Int) (result: Int) (h_precond : FindSingleNumber_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


#check FindSingleNumber.findUnique.induct
theorem FindSingleNumber_spec_satisfied (nums: List Int) (h_precond : FindSingleNumber_precond (nums)) :
    FindSingleNumber_postcond (nums) (FindSingleNumber (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold FindSingleNumber_postcond FindSingleNumber
  unfold FindSingleNumber_precond at h_precond
  --unfold FindSingleNumber_precond at h_precond
  constructor
  · --unfold FindSingleNumber_precond at h_precond
    grind
  constructor
  · -- 1. 进入函数定义
    --simp [FindSingleNumber]

    -- 2. 对递归函数进行归纳
    -- 注意：我们只需要对第一个参数（remaining）归纳，nums 在递归中是固定的上下文
    induction nums using FindSingleNumber.findUnique.induct (nums := nums) with
    | case1 =>
      -- 对应 remaining = [] 的情况
      -- 根据 precond，这种情况在逻辑上是矛盾的（因为一定存在一个 count=1 的数）
      -- 这里通常需要配合 h_precond 证出一个 False
      grind
    | case2 y ys filtered count h =>
      -- 对应 count ≠ 1，继续找下一个
      -- ih 是归纳假设：如果剩下的列表中有那个唯一数，那么结果正确
      unfold FindSingleNumber.findUnique
      codetic
      --codetic
    | case3 y ys filtered count h ih =>
      unfold FindSingleNumber.findUnique
      --codetic
      -- 对应 count = 1，函数返回 x
      -- 此时 res = x，目标变为 (filterlist x nums).length = 1
      -- 这正好就是 h_count_one 这个条件！
      --codetic




  -- !benchmark @end proof
