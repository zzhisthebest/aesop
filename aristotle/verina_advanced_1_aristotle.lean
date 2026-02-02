/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bd7b16a0-5ebe-4cc2-b6d8-ae8e981d5de1

The following was proved by Aristotle:

- theorem FindSingleNumber_spec_satisfied (nums: List Int) (h_precond : FindSingleNumber_precond (nums)) :
    FindSingleNumber_postcond (nums) (FindSingleNumber (nums) h_precond) h_precond
-/

-- import Mathlib
import Codetic
import Mathlib
set_option maxHeartbeats 0

namespace verina_advanced_1

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

theorem FindSingleNumber_spec_satisfied (nums: List Int) (h_precond : FindSingleNumber_precond (nums)) :
    FindSingleNumber_postcond (nums) (FindSingleNumber (nums) h_precond) h_precond := by
      -- By definition of `findUnique`, if the count of `x` in `nums` is 1, then `x` is the unique number.
      have h_unique : ∃ x ∈ nums, (filterlist x nums).length = 1 ∧ ∀ y ∈ nums, (filterlist y nums).length = 1 → y = x := by
        have h_unique : List.length (List.filter (fun x => (filterlist x nums).length = 1) nums) = 1 := by
          -- The length of the filtered list is equal to the count of 1s in the count list.
          have h_filter_eq_count : List.length (List.filter (fun x => (filterlist x nums).length = 1) nums) = List.count 1 (List.map (fun x => List.count x nums) nums) := by
            have h_filter_eq_count : ∀ x ∈ nums, (filterlist x nums).length = List.count x nums := by
              intro x hx
              have h_filter_length : ∀ (lst : List ℤ), (List.length (List.filter (fun y => y = x) lst)) = (List.count x lst) := by
                grind;
              -- By definition of `filterlist`, we have `filterlist x nums = List.filter (fun y => y = x) nums`.
              have h_filterlist_eq_filter : filterlist x nums = List.filter (fun y => y = x) nums := by
                -- By definition of `filterlist`, we have `filterlist x nums = List.filter (fun y => y = x) nums` because the auxiliary function recursively builds the list by including elements that match `x`.
                have h_filterlist_eq_filter : ∀ (lst : List ℤ), filterlist.aux x lst = List.filter (fun y => y = x) lst := by
                  -- We can prove this by induction on the list `lst`.
                  intro lst
                  induction' lst with y ys ih;
                  · rfl;
                  · by_cases hy : y = x <;> simp +decide [ *, verina_advanced_1.filterlist.aux ];
                exact h_filterlist_eq_filter nums;
              rw [ h_filterlist_eq_filter, h_filter_length ];
            rw [ List.count ];
            rw [ List.countP_map ];
            rw [ List.countP_eq_length_filter ];
            exact congr_arg List.length ( List.filter_congr fun x hx => by aesop );
          cases h_precond ; aesop;
        obtain ⟨ x, hx ⟩ := List.length_eq_one_iff.mp h_unique;
        -- Since the filtered list is [x], any element in the original list that is in the filtered list must be x.
        have hx_in_nums : x ∈ nums := by

          exact List.mem_of_mem_filter ( hx.symm ▸ List.mem_singleton_self _ );
        exact ⟨ x, hx_in_nums, by replace hx := congr_arg List.toFinset hx; rw [ Finset.ext_iff ] at hx; specialize hx x; aesop, fun y hy hy' => by replace hx := congr_arg List.toFinset hx; rw [ Finset.ext_iff ] at hx; specialize hx y; aesop ⟩;
      -- By definition of `findUnique`, it will return the unique element from `h_unique`.
      have h_findUnique : verina_advanced_1.FindSingleNumber.findUnique nums nums = h_unique.choose := by
        have h_findUnique : ∀ {remaining : List ℤ}, h_unique.choose ∈ remaining → verina_advanced_1.FindSingleNumber.findUnique nums remaining = h_unique.choose := by
          intros remaining h_remaining; induction' remaining with x xs ih <;> simp_all +decide ;
          by_cases hx : h_unique.choose = x <;> simp_all +decide [ verina_advanced_1.FindSingleNumber.findUnique ];
          · exact fun h => False.elim <| h <| hx ▸ h_unique.choose_spec.2.1;
          · exact fun h => h_unique.choose_spec.2.2 x ( by
              have h_filterlist : ∀ {x : ℤ} {nums : List ℤ}, (verina_advanced_1.filterlist x nums).length > 0 → x ∈ nums := by
                intros x nums h_filterlist_pos; induction' nums with y ys ih <;> simp_all +decide [ verina_advanced_1.filterlist ] ;
                · exact h_filterlist_pos.ne' ( by rfl );
                · unfold verina_advanced_1.filterlist.aux at h_filterlist_pos; aesop;
              exact h_filterlist ( by linarith ) ) h ▸ rfl;
        exact h_findUnique h_unique.choose_spec.1;
      -- Substitute h_findUnique into the postcondition.
      have h_postcond : (nums.length > 0) ∧ ((filterlist (h_unique.choose) nums).length = 1) ∧ (∀ x ∈ nums, (x = h_unique.choose) ∨ ((filterlist x nums).length = 2)) := by
        have := h_precond.1; simp_all +decide [ List.count ] ;
        -- By definition of `filterlist`, we know that `(filterlist x nums).length = List.countP (fun y => y = x) nums`.
        have h_filterlist_length : ∀ x ∈ nums, (filterlist x nums).length = List.countP (fun y => y = x) nums := by
          intros x hx
          have h_filterlist_aux : ∀ (lst : List ℤ), (filterlist.aux x lst).length = List.countP (fun y => y = x) lst := by
            intro lst; induction lst <;> simp +decide [ *, List.countP_cons ] ;
            · rfl;
            · split_ifs <;> simp_all [ verina_advanced_1.filterlist.aux ];
          exact h_filterlist_aux nums;
        -- By definition of `filterlist`, we know that `(filterlist x nums).length = List.countP (fun y => y = x) nums`. Therefore, we can use the hypothesis `this` to conclude the proof.
        have h_filterlist_length : ∀ x ∈ nums, (filterlist x nums).length = 1 ∨ (filterlist x nums).length = 2 := by
          codetic
        exact ⟨ List.length_pos_iff.mpr ( by rintro rfl; simpa using h_unique.choose_spec.1 ), h_unique.choose_spec.2.1, fun x hx => Classical.or_iff_not_imp_left.2 fun hx' => Or.resolve_left ( h_filterlist_length x hx ) fun hx'' => hx' <| h_unique.choose_spec.2.2 x hx hx'' ⟩;
      -- Since `findUnique` returns the unique element from `h_unique`, we can conclude that the postcondition holds.
      convert h_postcond using 1

end verina_advanced_1
#check List.prod_cons
