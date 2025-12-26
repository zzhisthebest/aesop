import Aesop
set_option maxHeartbeats 0
namespace tmp
def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums

@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1



def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  let rec findUnique (remaining : List Int) : Int :=
    match remaining with
    | [] =>
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

@[reducible]
def FindSingleNumber_postcond (nums : List Int) (result: Int) (h_precond : FindSingleNumber_precond (nums)) : Prop :=
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))

@[simp]
theorem filterlist_len_eq_count (x : Int) (nums : List Int) :
    (filterlist x nums).length = nums.count x := by
  unfold filterlist
  let rec aux_len (lst : List Int) : (filterlist.aux x lst).length = lst.count x := by
    induction lst with
    | nil => rfl
    | cons y ys ih =>
      simp [filterlist.aux, List.count_cons]
      split <;> simp [ih]
  apply aux_len

theorem findUnique_returns_single (nums : List Int)
    (h : FindSingleNumber_precond nums) :
    (filterlist (FindSingleNumber nums h) nums).length = 1:= by
  simp only [filterlist_len_eq_count]
  unfold FindSingleNumber

  -- 2. 准备存在性：证明 nums 中确实有一个元素的 count 是 1
  have :∃ x ∈ nums, nums.count x = 1 := by
    unfold FindSingleNumber_precond at h
    have h1 := h.right
    have h_mem : 1 ∈ nums.map (fun x => nums.count x) := by
      apply List.count_pos.mp
      omega
    rcases List.mem_map.mp h_mem with ⟨x, hx_in, hx_cnt⟩
    exact ⟨x, hx_in, hx_cnt⟩

  rcases this with ⟨target, h_target_in, h_target_cnt⟩

  -- 3. 对 findUnique 的输入列表进行归纳
  -- 注意：这里需要证明一个更强的命题：只要 target ∈ remaining，就能找到 count=1 的数
  let rec go (rem : List Int) (ht : target ∈ rem) :
      nums.count (FindSingleNumber.findUnique nums rem) = 1 := by
    match rem with
    | x :: xs =>
      simp [FindSingleNumber.findUnique]
      simp [filterlist_len_eq_count]
      split
      · -- 情况 1: 刚好在这个位置找到了 count = 1 的元素
        assumption
      · -- 情况 2: 当前元素 count ≠ 1，根据归纳假设在剩余列表 xs 中找
        apply go xs
        -- 这里需要证明 target 不可能是 x，所以一定在 xs 里
        simp at ht
        cases ht with
        | inl heq => subst heq; contradiction
        | inr hin => exact hin

  apply go nums h_target_in


end tmp
