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
theorem count_eq_len (x : Int) (nums : List Int) :
    nums.count x = (filterlist x nums).length:= by
  aesop
  simp_all only [filterlist]
  induction nums with
  | @nil =>
    unfold tmp.filterlist.aux
    simp_all only [List.count_nil, List.length_nil]
  | @cons a a_1 =>
    unfold tmp.filterlist.aux
    simp_all only
    split
    next tail_ih h =>
      subst h
      simp_all only [List.count_cons_self, List.length_cons, Nat.add_left_cancel_iff]
    next tail_ih h => simp_all only [ne_eq, not_false_eq_true, List.count_cons_of_ne]

--没有证明出来就是因为unfold是在h上而不是在target里进行的
theorem count_eq_one_iff_len_one (x : Int) (nums : List Int) :
    nums.count x = 1 ↔ (filterlist x nums).length = 1:= by
  aesop
  unfold filterlist
  constructor
  · aesop
    induction nums with
    | nil =>
      -- 基础情况：0 = 1，矛盾
      unfold filterlist.aux
      aesop
    | cons a_1 a_1_1 ih =>
      unfold filterlist.aux
      simp_all only
      split
      next h =>
        subst h
        simp_all only [List.count_cons_self, Nat.add_eq_right, List.length_cons, List.length_eq_zero_iff,
          Nat.zero_ne_one, false_implies]
        induction a_1_1 with
        | @nil =>
          unfold tmp.filterlist.aux
          simp_all only [List.count_nil]
        | @cons a_2 a_1_1 =>
          unfold tmp.filterlist.aux
          simp_all only
          split
          next tail_ih h =>
            subst h
            simp_all only [List.count_cons_self, Nat.add_eq_zero, Nat.succ_ne_self, and_false]
          next tail_ih h => simp_all only [ne_eq, not_false_eq_true, List.count_cons_of_ne]
      next h => simp_all only [ne_eq, not_false_eq_true, List.count_cons_of_ne]
  · induction nums with
  | nil =>
    -- 基础情况：0 = 1，矛盾
    unfold filterlist.aux
    aesop?
  | cons y ys ih =>
    unfold filterlist.aux
    -- 归纳步骤
    intro h
    split at h
    · -- 情况 y = x
      aesop

      -- induction ys with
      -- | nil =>
      --   unfold filterlist.aux at h
      --   aesop
      -- | cons z zs ih =>
      --   unfold filterlist.aux at h--没有证明出来就是因为unfold是在h上而不是在target里进行的
      --   aesop
    · aesop


end tmp
