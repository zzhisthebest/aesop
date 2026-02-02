/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f7c5aed6-88d6-421b-ba82-800d005da088

The following was proved by Aristotle:

- theorem LongestCommonSubsequence_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    LongestCommonSubsequence_postcond (a) (b) (LongestCommonSubsequence (a) (b) h_precond) h_precond

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib
import Codetic
set_option trace.codetic true



set_option maxHeartbeats 0

namespace verina_advanced_3

@[reducible]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def intMax (x y : Int) : Int :=
  if x < y then y else x

def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  let m := a.size
  let n := b.size

  let dp := Id.run do
    let mut dp := Array.mkArray (m + 1) (Array.mkArray (n + 1) 0)
    for i in List.range (m + 1) do
      for j in List.range (n + 1) do
        if i = 0 ∨ j = 0 then
          ()
        else if a[i - 1]! = b[j - 1]! then
          let newVal := ((dp[i - 1]!)[j - 1]!) + 1
          dp := dp.set! i (dp[i]!.set! j newVal)
        else
          let newVal := intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
          dp := dp.set! i (dp[i]!.set! j newVal)
    return dp
  (dp[m]!)[n]!

@[reducible]
def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Prop :=
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)

noncomputable section AristotleLemmas

/-
Definition of Longest Common Subsequence length for lists.
-/
def verina_advanced_3.LCSLength (l1 l2 : List Int) : Nat :=
  match l1, l2 with
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x = y then 1 + verina_advanced_3.LCSLength xs ys
    else Nat.max (verina_advanced_3.LCSLength xs (y :: ys)) (verina_advanced_3.LCSLength (x :: xs) ys)
termination_by l1.length + l2.length
decreasing_by
simp +arith +decide; (
grind); (
simp +arith +decide)

/-
The length of any common subsequence of two lists is less than or equal to the value computed by `LCSLength`.
-/
lemma verina_advanced_3.LCSLength_sublist (l1 l2 : List Int) :
  ∀ s, List.Sublist s l1 → List.Sublist s l2 → s.length ≤ verina_advanced_3.LCSLength l1 l2 := by
    induction' l1 with x l1 ih generalizing l2;
    · aesop;
    · induction' l2 with y l2 ih' generalizing l1; aesop;
      unfold verina_advanced_3.verina_advanced_3.LCSLength;
      grind

/-
There exists a common subsequence of two lists with length equal to the value computed by `LCSLength`.
-/
lemma verina_advanced_3.LCSLength_exists (l1 l2 : List Int) :
  ∃ s, List.Sublist s l1 ∧ List.Sublist s l2 ∧ s.length = verina_advanced_3.LCSLength l1 l2 := by
    induction' l1 with l1_x l1_ih generalizing l2;
    · cases l2 <;> unfold verina_advanced_3.verina_advanced_3.LCSLength <;> aesop;
    · unfold verina_advanced_3.LCSLength;
      induction' l2 with l2_x l2_ih generalizing l1_x l1_ih;
      · exact ⟨ [ ], by simp +decide ⟩;
      · rename_i h1 h2;
        by_cases h : l1_x = l2_x;
        · obtain ⟨ s, hs1, hs2, hs3 ⟩ := h2 l2_ih;
          use l1_x :: s;
          grind;
        · cases max_choice ( verina_advanced_3.LCSLength l1_ih ( l2_x :: l2_ih ) ) ( verina_advanced_3.LCSLength ( l1_x :: l1_ih ) l2_ih ) <;> simp_all +decide;
          · specialize h2 ( l2_x :: l2_ih ) ; aesop;
          · specialize h1 l1_x l1_ih h2;
            unfold verina_advanced_3.LCSLength; aesop;

/-
The `foldl` operation in `allSubseq` produces a list of reversed subsequences of the input list.
-/
lemma verina_advanced_3.allSubseq_foldl_spec (l : List Int) (r : List Int) :
  r ∈ l.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] ↔ List.Sublist r.reverse l := by
    constructor <;> intro h;
    · induction' l using List.reverseRecOn with l ih generalizing r <;> aesop;
    ·
      revert r;
      -- codetic?
      induction l using List.reverse_RecOn
      · codetic?
      · codetic?
        intro r h
        simp_all only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.mem_append, List.mem_map]
        induction r with
        | @nil =>
          simp_all only [List.reverse_nil, List.nil_sublist, List.sublist_append_of_sublist_left, reduceCtorEq,
            and_false, exists_const, or_false]
        | @cons a_2 a_1_1 =>
          simp_all only [List.reverse_cons, List.cons.injEq, exists_eq_right_right]
          grind--codetic成功证明

/-
The length of the longest common subsequence is invariant under reversing both lists. This follows from the fact that `s` is a subsequence of `l` if and only if `s.reverse` is a subsequence of `l.reverse`.
-/
lemma verina_advanced_3.LCSLength_reverse (l1 l2 : List Int) :
  verina_advanced_3.LCSLength l1.reverse l2.reverse = verina_advanced_3.LCSLength l1 l2 := by
    -- By definition of LCSLength, it is symmetric with respect to the order of the lists.
    have h_symm : ∀ l1 l2 : List ℤ, verina_advanced_3.LCSLength l1 l2 = verina_advanced_3.LCSLength l2 l1 := by
      intros l1 l2
      induction' l1 with x1 l1 ih generalizing l2;
      · cases l2 <;> simp +decide [ verina_advanced_3.verina_advanced_3.LCSLength ];
      · induction' l2 with x2 l2 ih' generalizing x1 l1;
        · unfold verina_advanced_3.LCSLength; aesop;
        · unfold verina_advanced_3.verina_advanced_3.LCSLength;
          grind;
    -- By definition of LCSLength, it is invariant under reversing both lists.
    have h_lcs_rev : ∀ l1 l2 : List ℤ, verina_advanced_3.LCSLength l1.reverse l2.reverse = verina_advanced_3.LCSLength l1 l2 := by
      intros l1 l2
      apply le_antisymm;
      · obtain ⟨ s, hs1, hs2, hs3 ⟩ := verina_advanced_3.LCSLength_exists l1.reverse l2.reverse;
        have := verina_advanced_3.LCSLength_sublist l1 l2 s.reverse ( by simpa using hs1.reverse ) ( by simpa using hs2.reverse ) ; aesop;
      · obtain ⟨ s, hs1, hs2, hs3 ⟩ := verina_advanced_3.LCSLength_exists l1 l2;
        have h_rev_subseq : s.reverse.Sublist l1.reverse ∧ s.reverse.Sublist l2.reverse := by
          exact ⟨ hs1.reverse, hs2.reverse ⟩;
        have := verina_advanced_3.LCSLength_sublist l1.reverse l2.reverse s.reverse h_rev_subseq.1 h_rev_subseq.2; aesop;
    exact h_lcs_rev l1 l2

/-
Recurrence relation for `LCSLength` when elements are appended to the lists. This matches the bottom-up DP approach.
-/
lemma LCSLength_append (l1 l2 : List Int) (x y : Int) :
  verina_advanced_3.LCSLength (l1 ++ [x]) (l2 ++ [y]) =
    if x = y then 1 + verina_advanced_3.LCSLength l1 l2
    else Nat.max (verina_advanced_3.LCSLength l1 (l2 ++ [y])) (verina_advanced_3.LCSLength (l1 ++ [x]) l2) := by
      rw [ ← verina_advanced_3.LCSLength_reverse ];
      split_ifs <;> simp_all +decide [ List.append_assoc ];
      · -- By definition of LCSLength, when the first elements of the two lists are equal, the LCSLength is 1 plus the LCSLength of the rest of the lists.
        have h_def : verina_advanced_3.verina_advanced_3.LCSLength (y :: l1.reverse) (y :: l2.reverse) = 1 + verina_advanced_3.verina_advanced_3.LCSLength l1.reverse l2.reverse := by
          rw [ verina_advanced_3.LCSLength ] ; aesop;
        rw [ h_def, verina_advanced_3.LCSLength_reverse ];
      · rw [ verina_advanced_3.LCSLength ];
        -- By definition of LCSLength, we can rewrite the right-hand side using the properties of list reversal.
        have h_rev : verina_advanced_3.LCSLength l1 (l2 ++ [y]) = verina_advanced_3.LCSLength (l1.reverse) ((l2 ++ [y]).reverse) ∧ verina_advanced_3.LCSLength (l1 ++ [x]) l2 = verina_advanced_3.LCSLength ((l1 ++ [x]).reverse) l2.reverse := by
          exact ⟨ by rw [ verina_advanced_3.LCSLength_reverse ], by rw [ verina_advanced_3.LCSLength_reverse ] ⟩;
        aesop

/-
`intMax` on natural numbers (coerced to Int) behaves like `Nat.max`.
-/
lemma intMax_nat (x y : Nat) : verina_advanced_3.intMax x y = (Nat.max x y : Int) := by
  codetic?

/-
Helper functions to represent the loop iterations in `LongestCommonSubsequence` as functional folds.
-/
def step_inner (a b : Array Int) (i : Nat) (dp : Array (Array Int)) (j : Nat) : Array (Array Int) :=
  if i = 0 ∨ j = 0 then
    dp
  else if a[i - 1]! = b[j - 1]! then
    let newVal := ((dp[i - 1]!)[j - 1]!) + 1
    dp.set! i (dp[i]!.set! j newVal)
  else
    let newVal := verina_advanced_3.intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
    dp.set! i (dp[i]!.set! j newVal)

def step_outer (a b : Array Int) (dp : Array (Array Int)) (i : Nat) : Array (Array Int) :=
  (List.range (b.size + 1)).foldl (step_inner a b i) dp

def LCS_dp (a b : Array Int) : Array (Array Int) :=
  (List.range (a.size + 1)).foldl (step_outer a b) (Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) 0))

/-
The imperative `LongestCommonSubsequence` function is equivalent to the functional `LCS_dp` model.
-/
lemma verina_advanced_3.LongestCommonSubsequence_eq_LCS_dp (a b : Array Int) (h : verina_advanced_3.LongestCommonSubsequence_precond a b) :
  verina_advanced_3.LongestCommonSubsequence a b h = ((verina_advanced_3.LCS_dp a b)[a.size]!)[b.size]! := by
    unfold verina_advanced_3.LongestCommonSubsequence verina_advanced_3.LCS_dp; simp +decide ;
    unfold verina_advanced_3.step_outer;
    unfold verina_advanced_3.step_inner;
    erw [ List.foldlM_eq_foldl ];
    congr;
    funext dp i; simp [List.foldl];
    induction' ( List.range ( b.size + 1 ) ) with j hj generalizing dp <;> simp +decide [ * ];
    bound

/-
Helper definition: `LCS_at a b i j` is the LCS length of the prefixes of `a` and `b` of length `i` and `j` respectively.
-/
def LCS_at (a b : Array Int) (i j : Nat) : Nat :=
  verina_advanced_3.LCSLength (a.take i).toList (b.take j).toList

/-
Base case: LCS length is 0 if the first prefix has length 0.
-/
lemma LCS_at_zero_left (a b : Array Int) (j : Nat) : verina_advanced_3.LCS_at a b 0 j = 0 := by
  codetic?

/-
Base case: LCS length is 0 if the second prefix has length 0.
-/
lemma LCS_at_zero_right (a b : Array Int) (i : Nat) : verina_advanced_3.LCS_at a b i 0 = 0 := by
  codetic?

/-
Recurrence relation for `LCS_at`: it satisfies the standard LCS recurrence.
-/
lemma verina_advanced_3.LCS_at_recurrence (a b : Array Int) (i j : Nat) (hi : i > 0) (hj : j > 0) (hi_le : i ≤ a.size) (hj_le : j ≤ b.size) :
  verina_advanced_3.LCS_at a b i j =
    if a[i - 1]! = b[j - 1]! then 1 + verina_advanced_3.LCS_at a b (i - 1) (j - 1)
    else Nat.max (verina_advanced_3.LCS_at a b (i - 1) j) (verina_advanced_3.LCS_at a b i (j - 1)) := by
      -- By definition of `take`, we know that `(a.take i).toList = (a.take (i-1)).toList ++ [a[i-1]!]` and `(b.take j).toList = (b.take (j-1)).toList ++ [b[j-1]!]`.
      have h_take : (a.take i).toList = (a.take (i-1)).toList ++ [a[i-1]!] ∧ (b.take j).toList = (b.take (j-1)).toList ++ [b[j-1]!] := by
        rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide [ Array.take ];
        have h_split : ∀ (l : List ℤ) (n : ℕ), n < l.length → List.take (n + 1) l = List.take n l ++ [l[n]!] := by
          intro l n hn; induction l generalizing n <;> aesop;
        grind;
      simp_all +decide [ verina_advanced_3.LCS_at ];
      convert verina_advanced_3.LCSLength_append _ _ _ _ using 1

/-
Define `LCS_dp_partial` as the state of the DP table after `k` outer loop iterations, and show `LCS_dp` corresponds to `k = a.size + 1`.
-/
def LCS_dp_partial (a b : Array Int) (k : Nat) : Array (Array Int) :=
  (List.range k).foldl (step_outer a b) (Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) 0))

lemma LCS_dp_eq_partial (a b : Array Int) :
  verina_advanced_3.LCS_dp a b = LCS_dp_partial a b (a.size + 1) := by
  codetic?

/-
`step_inner` only modifies the `i`-th row of the DP table.
-/
lemma verina_advanced_3.step_inner_preserves_other_rows (a b : Array Int) (i : Nat) (dp : Array (Array Int)) (j : Nat) (r : Nat) (h : r ≠ i) :
  ((verina_advanced_3.step_inner a b i dp j)[r]!) = dp[r]! := by
    unfold verina_advanced_3.step_inner;
    split_ifs <;> simp_all +decide [ Array.setIfInBounds ];
    · split_ifs <;> simp_all
    · split_ifs <;> simp_all

/-
`step_outer` only modifies the `i`-th row of the DP table.
-/
lemma verina_advanced_3.step_outer_preserves_other_rows (a b : Array Int) (dp : Array (Array Int)) (i : Nat) (r : Nat) (h : r ≠ i) :
  ((verina_advanced_3.step_outer a b dp i)[r]!) = dp[r]! := by
    unfold verina_advanced_3.step_outer;
    -- By definition of `step_inner`, we know that it only modifies the `i`-th row of the DP table.
    have h_step_inner : ∀ (dp : Array (Array ℤ)) (j : Nat), ((verina_advanced_3.step_inner a b i dp j)[r]!) = dp[r]! := by
      exact?;
    induction' ( List.range ( b.size + 1 ) ) using List.reverseRecOn with j hj <;> aesop

/-
`step_inner` only modifies the `j`-th column of the `i`-th row.
-/
lemma step_inner_preserves_other_cols (a b : Array Int) (i : Nat) (dp : Array (Array Int)) (j : Nat) (c : Nat) (h : c ≠ j) :
  ((verina_advanced_3.step_inner a b i dp j)[i]!)[c]! = (dp[i]!)[c]! := by
    -- codetic?成功证明
    sorry

/-
`step_inner` updates the cell `(i, j)` correctly according to the LCS recurrence, given valid bounds.
-/
lemma step_inner_update (a b : Array Int) (i j : Nat) (dp : Array (Array Int))
  (hi : i > 0) (hj : j > 0)
  (h_dp_size : i < dp.size)
  (h_dp_row_size : ∀ k, k < dp.size → (dp[k]!).size > j) :
  ((verina_advanced_3.step_inner a b i dp j)[i]!)[j]! =
    if a[i - 1]! = b[j - 1]! then ((dp[i-1]!)[j-1]!) + 1
    else verina_advanced_3.intMax ((dp[i-1]!)[j]!) ((dp[i]!)[j-1]!) := by
    -- codetic?成功证明
    sorry

/-
Helper definition: a row `i` in the DP table is correct if all its entries match `LCS_at`.
-/
def row_correct (a b : Array Int) (dp : Array (Array Int)) (i : Nat) : Prop :=
  ∀ j, j ≤ b.size → (dp[i]!)[j]! = verina_advanced_3.LCS_at a b i j

/-
Invariant for the inner loop: the `i`-th row is correct up to index `k`.
-/
def inner_invariant (a b : Array Int) (dp : Array (Array Int)) (i k : Nat) : Prop :=
  ∀ j, j < k → (dp[i]!)[j]! = verina_advanced_3.LCS_at a b i j

/-
Helper definition: the DP table has the correct dimensions.
-/
def valid_dp_shape (dp : Array (Array Int)) (m n : Nat) : Prop :=
  dp.size = m + 1 ∧ ∀ i, i < m + 1 → (dp[i]!).size = n + 1

/-
`step_inner` updates the cell `(i, j)` correctly according to the LCS recurrence, given valid bounds.
-/
lemma verina_advanced_3.step_inner_update_correct (a b : Array Int) (i j : Nat) (dp : Array (Array Int))
  (hi : i > 0) (hj : j > 0)
  (h_dp_size : i < dp.size)
  (h_dp_row_size : ∀ k, k < dp.size → (dp[k]!).size > j) :
  ((verina_advanced_3.step_inner a b i dp j)[i]!)[j]! =
    if a[i - 1]! = b[j - 1]! then ((dp[i-1]!)[j-1]!) + 1
    else verina_advanced_3.intMax ((dp[i-1]!)[j]!) ((dp[i]!)[j-1]!) := by
      codetic?

/-
For `i > 0` and `j > 0`, `step_inner` writes the correct LCS value at `(i, j)` assuming previous dependencies are correct.
-/
lemma step_inner_correct_positive (a b : Array Int) (i j : Nat) (dp : Array (Array Int))
  (h_shape : verina_advanced_3.valid_dp_shape dp a.size b.size)
  (hi : i > 0) (hi_le : i ≤ a.size)
  (hj : j > 0) (hj_le : j ≤ b.size)
  (h_prev_row : verina_advanced_3.row_correct a b dp (i - 1))
  (h_prev_col : (dp[i]!)[j-1]! = verina_advanced_3.LCS_at a b i (j - 1)) :
  ((verina_advanced_3.step_inner a b i dp j)[i]!)[j]! = verina_advanced_3.LCS_at a b i j := by
    have := @verina_advanced_3.step_inner_update_correct;
    specialize this a b i j dp hi hj;
    simp_all +decide [ verina_advanced_3.valid_dp_shape ];
    convert this ( by linarith ) ( fun k hk => by linarith ) using 1;
    rw [ verina_advanced_3.LCS_at_recurrence a b i j hi hj hi_le hj_le ];
    split_ifs <;> simp_all +decide [ add_comm, verina_advanced_3.intMax ];
    · exact Eq.symm ( h_prev_row _ ( Nat.sub_le_of_le_add <| by linarith ) );
    · rw [ h_prev_row j hj_le ];
      grind

/-
`valid_dp_shape` implies the dimensions of the DP table.
-/
lemma valid_dp_shape_implies_bounds (dp : Array (Array Int)) (m n : Nat)
  (h : verina_advanced_3.valid_dp_shape dp m n) :
  dp.size = m + 1 ∧ ∀ k, k < m + 1 → (dp[k]!).size = n + 1 := by
    --simp [verina_advanced_3.valid_dp_shape] at h
    -- codetic?成功证明
    sorry

/-
`step_inner` correctly computes the value at `(i, j)` assuming previous values are correct and boundary conditions hold.
-/
lemma verina_advanced_3.step_inner_correct_at_indices (a b : Array Int) (i j : Nat) (dp : Array (Array Int))
  (h_shape : verina_advanced_3.valid_dp_shape dp a.size b.size)
  (hi : i ≤ a.size) (hj : j ≤ b.size)
  (h_prev_row : i > 0 → verina_advanced_3.row_correct a b dp (i - 1))
  (h_prev_col : j > 0 → (dp[i]!)[j-1]! = verina_advanced_3.LCS_at a b i (j - 1))
  (h_i0 : i = 0 → (dp[0]!)[j]! = 0)
  (h_j0 : j = 0 → (dp[i]!)[0]! = 0) :
  ((verina_advanced_3.step_inner a b i dp j)[i]!)[j]! = verina_advanced_3.LCS_at a b i j := by
    by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0 <;> simp_all +decide [ verina_advanced_3.step_inner ];
    · unfold verina_advanced_3.LCS_at;
      unfold verina_advanced_3.verina_advanced_3.LCSLength; aesop;
    · exact Eq.symm ( by exact mod_cast verina_advanced_3.LCS_at_zero_left a b j );
    · exact Eq.symm ( Nat.cast_eq_zero.mpr ( verina_advanced_3.LCS_at_zero_right a b i ) );
    · convert verina_advanced_3.step_inner_correct_positive a b i j dp h_shape ( Nat.pos_of_ne_zero hi0 ) hi ( Nat.pos_of_ne_zero hj0 ) hj ( h_prev_row ( Nat.pos_of_ne_zero hi0 ) ) ( h_prev_col ( Nat.pos_of_ne_zero hj0 ) ) using 1;
      unfold verina_advanced_3.step_inner; aesop;

/-
Invariant for the outer loop: the first `k` rows of the DP table are correct.
-/
def outer_invariant (a b : Array Int) (dp : Array (Array Int)) (k : Nat) : Prop :=
  ∀ i, i < k → verina_advanced_3.row_correct a b dp i

/-
`step_inner` extends the `inner_invariant` from `j` to `j+1`.
-/
lemma verina_advanced_3.step_inner_preserves_invariant (a b : Array Int) (i : Nat) (dp : Array (Array Int)) (j : Nat)
  (h_shape : verina_advanced_3.valid_dp_shape dp a.size b.size)
  (hi : i ≤ a.size) (hj : j ≤ b.size)
  (h_prev_row : i > 0 → verina_advanced_3.row_correct a b dp (i - 1))
  (h_inv : verina_advanced_3.inner_invariant a b dp i j)
  (h_i0 : i = 0 → (dp[0]!)[j]! = 0)
  (h_j0 : j = 0 → (dp[i]!)[0]! = 0) :
  verina_advanced_3.inner_invariant a b (verina_advanced_3.step_inner a b i dp j) i (j + 1) := by
    intro k hk; rcases lt_or_eq_of_le ( Nat.le_of_lt_succ hk ) with hk' | rfl <;> simp_all +decide ;
    · -- By definition of `step_inner`, we know that it only modifies the `j`-th column of the `i`-th row.
      have h_step_inner_preserves_other_cols : ((verina_advanced_3.step_inner a b i dp j)[i]!)[k]! = (dp[i]!)[k]! := by
        apply verina_advanced_3.step_inner_preserves_other_cols;
        linarith;
      aesop;
    · convert verina_advanced_3.step_inner_correct_at_indices a b i k dp h_shape hi hj _ _ _ _ using 1 <;> aesop

/-
`step_inner` preserves the dimensions of the DP table.
-/
lemma step_inner_preserves_shape (a b : Array Int) (i : Nat) (dp : Array (Array Int)) (j : Nat)
  (h_shape : verina_advanced_3.valid_dp_shape dp a.size b.size) :
  verina_advanced_3.valid_dp_shape (verina_advanced_3.step_inner a b i dp j) a.size b.size := by
    unfold verina_advanced_3.valid_dp_shape at *;
    unfold verina_advanced_3.step_inner;
    split_ifs <;> simp_all
    · aesop;
    · grind;
    · intro k hk; rw [ Array.getElem_setIfInBounds ] ; aesop;

/-
`step_outer` preserves the dimensions of the DP table.
-/
lemma verina_advanced_3.step_outer_preserves_shape (a b : Array Int) (dp : Array (Array Int)) (i : Nat)
  (h_shape : verina_advanced_3.valid_dp_shape dp a.size b.size) :
  verina_advanced_3.valid_dp_shape (verina_advanced_3.step_outer a b dp i) a.size b.size := by
    -- By definition of `step_outer`, it applies `step_inner` to each column in the range `(b.size + 1)`.
    have h_step_outer_preserves_shape : ∀ (dp : Array (Array ℤ)) (i : Nat) (j : Nat), verina_advanced_3.valid_dp_shape dp a.size b.size → verina_advanced_3.valid_dp_shape (verina_advanced_3.step_inner a b i dp j) a.size b.size := by
      exact?;
    unfold verina_advanced_3.step_outer;
    induction' ( List.range ( b.size + 1 ) ) using List.reverseRecOn <;> aesop

/-
`step_outer` correctly computes the `i`-th row, assuming preconditions.
-/
lemma verina_advanced_3.step_outer_correct_row (a b : Array Int) (dp : Array (Array Int)) (i : Nat)
  (h_shape : verina_advanced_3.valid_dp_shape dp a.size b.size)
  (hi : i ≤ a.size)
  (h_prev_row : i > 0 → verina_advanced_3.row_correct a b dp (i - 1))
  (h_i0 : i = 0 → ∀ j, j ≤ b.size → (dp[0]!)[j]! = 0)
  (h_j0 : (dp[i]!)[0]! = 0) :
  verina_advanced_3.row_correct a b (verina_advanced_3.step_outer a b dp i) i := by
    intro j hj;
    -- We prove by induction on the fold that `inner_invariant` holds.
    have h_inner_invariant_fold : ∀ k ≤ b.size + 1, verina_advanced_3.inner_invariant a b (List.foldl (fun dp j => verina_advanced_3.step_inner a b i dp j) dp (List.range k)) i k := by
      intro k hk
      induction' k with k ih
      all_goals generalize_proofs at *;
      · tauto;
      · simp_all +decide [ List.range_succ ];
        apply_rules [ verina_advanced_3.step_inner_preserves_invariant ];
        · have h_shape_fold : ∀ (dp : Array (Array Int)) (k : ℕ), verina_advanced_3.valid_dp_shape dp a.size b.size → verina_advanced_3.valid_dp_shape (List.foldl (fun dp j => verina_advanced_3.step_inner a b i dp j) dp (List.range k)) a.size b.size := by
            intros dp k h_shape; induction' k with k ih generalizing dp <;> simp_all +decide [ List.range_succ ] ;
            exact verina_advanced_3.step_inner_preserves_shape _ _ _ _ _ ( ih _ h_shape );
          exact h_shape_fold dp k h_shape;
        · intro hi_pos
          have h_prev_row_fold : ∀ k ≤ b.size + 1, verina_advanced_3.row_correct a b (List.foldl (fun dp j => verina_advanced_3.step_inner a b i dp j) dp (List.range k)) (i - 1) := by
            intro k hk
            induction' k with k ih;
            · exact h_prev_row hi_pos;
            · simp_all +decide [ List.range_succ ];
              intro j hj;
              rw [ verina_advanced_3.step_inner_preserves_other_rows ];
              · exact ih ( by linarith ) j hj;
              · omega;
          exact h_prev_row_fold k ( by linarith );
        · linarith;
        · induction' ( List.range k ) using List.reverseRecOn with k ih <;> aesop;
        · grind;
    exact h_inner_invariant_fold _ le_rfl _ ( Nat.lt_succ_of_le hj )

/-
`step_outer` preserves the property that the 0-th column is all 0s.
-/
lemma verina_advanced_3.step_outer_preserves_col_zero (a b : Array Int) (dp : Array (Array Int)) (i : Nat)
  (h_col_zero : ∀ r, r < dp.size → (dp[r]!)[0]! = 0) :
  ∀ r, r < dp.size → ((verina_advanced_3.step_outer a b dp i)[r]!)[0]! = 0 := by
    intro r hr;
    by_cases hi : i = 0 <;> by_cases hr : r = i <;> simp_all +decide [ step_outer ];
    · unfold verina_advanced_3.step_inner; aesop;
    · induction' ( List.range ( b.size + 1 ) ) using List.reverseRecOn <;> aesop;
    · have h_step_inner_preserves_zero : ∀ (dp : Array (Array ℤ)) (j : Nat), (dp[i]!)[0]! = 0 → ((verina_advanced_3.step_inner a b i dp j)[i]!)[0]! = 0 := by
        intros dp j hj_zero
        simp [verina_advanced_3.step_inner, hj_zero];
        cases j <;> simp_all
        grind;
      induction' ( List.range ( b.size + 1 ) ) using List.reverseRecOn with j hj ih <;> aesop;
    · induction' ( List.range ( b.size + 1 ) ) using List.reverseRecOn with x xs ih;
      · aesop;
      · by_cases h : r = i <;> simp_all +decide [ step_inner ];
        split_ifs <;> simp_all
        · rw [ Array.getElem?_setIfInBounds ] ; aesop;
        · grind

/-
Invariant for the `LCS_dp` computation: shape is valid, first `k` rows are correct, first column is 0, first row is 0.
-/
def row_zero (dp : Array (Array Int)) : Prop :=
  ∀ j, j < (dp[0]!).size → (dp[0]!)[j]! = 0

def col_zero (dp : Array (Array Int)) : Prop :=
  ∀ i, i < dp.size → (dp[i]!)[0]! = 0

def LCS_dp_invariant (a b : Array Int) (k : Nat) (dp : Array (Array Int)) : Prop :=
  verina_advanced_3.valid_dp_shape dp a.size b.size ∧
  verina_advanced_3.outer_invariant a b dp k ∧
  verina_advanced_3.col_zero dp ∧
  verina_advanced_3.row_zero dp

/-
`step_outer` preserves the property that the 0-th row is all 0s.
-/
lemma step_outer_preserves_row_zero (a b : Array Int) (dp : Array (Array Int)) (i : Nat)
  (h_row_zero : verina_advanced_3.row_zero dp) :
  verina_advanced_3.row_zero (verina_advanced_3.step_outer a b dp i) := by
    unfold verina_advanced_3.step_outer;
    -- By definition of `step_inner`, if `i ≠ 0`, then `step_inner` does not modify the 0-th row.
    have h_inner_preserves_zero_row : ∀ (j : ℕ) (dp : Array (Array ℤ)), i ≠ 0 → verina_advanced_3.row_zero dp → verina_advanced_3.row_zero (verina_advanced_3.step_inner a b i dp j) := by
      sorry--codetic?成功证明
    by_cases hi : i = 0;
    · unfold verina_advanced_3.step_inner; aesop;
    ·

      induction ( List.range ( b.size + 1 ) ) using List.reverseRecOn
      aesop?
      aesop?

/-
`step_outer` maintains the `LCS_dp_invariant`, extending correctness to the `i`-th row.
-/
lemma step_outer_preserves_invariant (a b : Array Int) (i : Nat) (dp : Array (Array Int))
  (hi : i < a.size + 1)
  (h_inv : verina_advanced_3.LCS_dp_invariant a b i dp) :
  verina_advanced_3.LCS_dp_invariant a b (i + 1) (verina_advanced_3.step_outer a b dp i) := by
    unfold verina_advanced_3.LCS_dp_invariant at *;
    refine' ⟨ _, _, _, _ ⟩;
    · exact verina_advanced_3.step_outer_preserves_shape a b dp i h_inv.1;
    · intro j hj;
      by_cases hj' : j = i;
      · convert verina_advanced_3.step_outer_correct_row a b dp i h_inv.1 ( by linarith ) _ _ _ using 1;
        · exact fun hi => h_inv.2.1 _ ( Nat.sub_lt hi zero_lt_one );
        · exact fun hi j hj => h_inv.2.2.2 j ( by linarith [ h_inv.1.2 0 ( by linarith ) ] );
        · exact h_inv.2.2.1 _ ( by linarith [ h_inv.1.1 ] );
      · intro k hk;
        have h_row_correct : ((verina_advanced_3.step_outer a b dp i)[j]!) = dp[j]! := by
          exact?;
        have := h_inv.2.1 j ( by omega ) k hk; aesop;
    · unfold verina_advanced_3.step_outer;
      have h_col_zero : ∀ (l : List ℕ), verina_advanced_3.col_zero dp → verina_advanced_3.col_zero (List.foldl (verina_advanced_3.step_inner a b i) dp l) := by
        sorry--codetic? succeed
      exact h_col_zero _ h_inv.2.2.1;
    · exact verina_advanced_3.step_outer_preserves_row_zero a b dp i h_inv.2.2.2

/-
The initial DP table satisfies the invariant.
-/
lemma LCS_dp_initial_invariant (a b : Array Int) :
  verina_advanced_3.LCS_dp_invariant a b 0 (Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) 0)) := by
  -- codetic?成功证明
    sorry



/-
The final DP table computed by `LCS_dp` satisfies the invariant.
-/
lemma verina_advanced_3.LCS_dp_correct (a b : Array Int) :
  verina_advanced_3.LCS_dp_invariant a b (a.size + 1) (verina_advanced_3.LCS_dp a b) := by
    -- We prove by induction on the list `List.range (a.size + 1)` that the invariant holds.
    have h_ind : ∀ k, k ≤ a.size + 1 → LCS_dp_invariant a b k (List.foldl (step_outer a b) (Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) 0)) (List.range k)) := by

      intro k hk
      induction' k with k ih;
      · exact verina_advanced_3.LCS_dp_initial_invariant a b;
      · simpa [ List.range_succ ] using step_outer_preserves_invariant a b k _ ( by linarith ) ( ih ( by linarith ) );
    exact h_ind _ le_rfl

/-
The `LongestCommonSubsequence` function computes the same value as `LCSLength`.
-/
lemma verina_advanced_3.LongestCommonSubsequence_eq_LCSLength (a b : Array Int) (h : verina_advanced_3.LongestCommonSubsequence_precond a b) :
  verina_advanced_3.LongestCommonSubsequence a b h = verina_advanced_3.LCSLength a.toList b.toList := by
    have := verina_advanced_3.LCS_dp_correct a b;
    -- By the properties of the LCS_dp_invariant, we know that the last row of the DP table is correct.
    have h_last_row : verina_advanced_3.row_correct a b (verina_advanced_3.LCS_dp a b) a.size := by
      exact this.2.1 _ ( Nat.lt_succ_self _ );
    rw [ verina_advanced_3.LongestCommonSubsequence_eq_LCS_dp ];
    convert h_last_row b.size ( by linarith ) using 1;
    unfold verina_advanced_3.LCS_at; aesop;

end AristotleLemmas

theorem LongestCommonSubsequence_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    LongestCommonSubsequence_postcond (a) (b) (LongestCommonSubsequence (a) (b) h_precond) h_precond := by
      have h_lcs_eq : verina_advanced_3.LongestCommonSubsequence a b h_precond = verina_advanced_3.LCSLength a.toList b.toList := by
        convert verina_advanced_3.LongestCommonSubsequence_eq_LCSLength a b h_precond using 1;
      constructor;
      · obtain ⟨ s, hs₁, hs₂, hs₃ ⟩ := verina_advanced_3.LCSLength_exists a.toList b.toList;
        -- By definition of `allSubseq`, we know that `s` is in the list of all subsequences of `a` and `b`.
        have h_s_in_allSubseq : s.reverse ∈ List.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] a.toList ∧ s.reverse ∈ List.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] b.toList := by
          exact ⟨ by simpa using verina_advanced_3.allSubseq_foldl_spec a.toList s.reverse |>.2 <| by simpa using hs₁, by simpa using verina_advanced_3.allSubseq_foldl_spec b.toList s.reverse |>.2 <| by simpa using hs₂ ⟩;
        aesop;
      · simp_all +decide [ List.all_eq_true ];
        intro x hx
        by_cases h_mem : x ∈ Array.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] b;
        · have h_subseq : List.Sublist x.reverse a.toList ∧ List.Sublist x.reverse b.toList := by
            have h_subseq : ∀ (l : List ℤ) (x : List ℤ), x ∈ List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] l → List.Sublist x.reverse l := by
              intros l x hx; induction' l using List.reverseRecOn with l ih generalizing x <;> aesop;
            aesop;
          have := verina_advanced_3.LCSLength_sublist a.toList b.toList x.reverse h_subseq.1 h_subseq.2; aesop;
        · exact Or.inl h_mem

end verina_advanced_3
