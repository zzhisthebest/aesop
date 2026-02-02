/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1d10d262-cf2f-448b-8a8a-306d38b39974

The following was proved by Aristotle:

- theorem addTwoNumbers_spec_satisfied (l1: List Nat) (l2: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    addTwoNumbers_postcond (l1) (l2) (addTwoNumbers (l1) (l2) h_precond) h_precond

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Codetic
import Mathlib




set_option maxHeartbeats 0

namespace verina_advanced_5

def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds

@[reducible]
def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])

def addTwoNumbers (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : List Nat :=
  let rec addAux (l1 l2 : List Nat) (carry : Nat) : List Nat :=
    match l1, l2 with
    | [], [] =>
      if carry = 0 then [] else [carry]
    | h1::t1, [] =>
      let sum := h1 + carry
      (sum % 10) :: addAux t1 [] (sum / 10)
    | [], h2::t2 =>
      let sum := h2 + carry
      (sum % 10) :: addAux [] t2 (sum / 10)
    | h1::t1, h2::t2 =>
      let sum := h1 + h2 + carry
      (sum % 10) :: addAux t1 t2 (sum / 10)
  addAux l1 l2 0

@[reducible]
def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : Prop :=
  listToNat result = listToNat l1 + listToNat l2 ∧
  (∀ d ∈ result, d < 10) ∧
  (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0]))

noncomputable section Aristotletheorems

#check verina_advanced_5.addTwoNumbers.addAux

/-
The listToNat of the result of addAux is the sum of listToNat of inputs plus carry.
-/
lemma addAux_listToNat (l1 l2 : List Nat) (carry : Nat) :
  listToNat (verina_advanced_5.addTwoNumbers.addAux l1 l2 carry) = listToNat l1 + listToNat l2 + carry := by
    induction' l1 with d1 t1 ih generalizing l2 carry <;> induction' l2 with d2 t2 ih' generalizing carry <;> simp +arith +decide [ * ];
    · unfold verina_advanced_5.addTwoNumbers.addAux; aesop;
    · -- By definition of `addAux`, we can split the addition into the sum of the heads and the sum of the tails.
      have h_split : verina_advanced_5.addTwoNumbers.addAux [] (d2 :: t2) carry = (d2 + carry) % 10 :: verina_advanced_5.addTwoNumbers.addAux [] t2 ((d2 + carry) / 10) := by
        -- By definition of `addAux`, when the first list is empty and the second list is non-empty, it adds the carry to the head of the second list and then recursively processes the tail.
        rw [verina_advanced_5.addTwoNumbers.addAux];
      simp +arith +decide [ *, verina_advanced_5.listToNat ];
      rw [ Nat.div_add_mod ];
    · specialize ih [ ] ( ( d1 + carry ) / 10 ) ; simp_all +arith +decide [ verina_advanced_5.listToNat ];
      -- By definition of `listToNat`, we can split the list into the head `d1` and the tail `t1`.
      have h_split : verina_advanced_5.listToNat (verina_advanced_5.addTwoNumbers.addAux (d1 :: t1) [] carry) = (d1 + carry) % 10 + 10 * verina_advanced_5.listToNat (verina_advanced_5.addTwoNumbers.addAux t1 [] ((d1 + carry) / 10)) := by
        rw [verina_advanced_5.addTwoNumbers.addAux];
        exact?;
      grind;
    · unfold verina_advanced_5.addTwoNumbers.addAux; simp +arith +decide [ ih, ih' ];
      rw [ show verina_advanced_5.listToNat ( ( d1 + d2 + carry ) % 10 :: verina_advanced_5.addTwoNumbers.addAux t1 t2 ( ( d1 + d2 + carry ) / 10 ) ) = ( d1 + d2 + carry ) % 10 + 10 * verina_advanced_5.listToNat ( verina_advanced_5.addTwoNumbers.addAux t1 t2 ( ( d1 + d2 + carry ) / 10 ) ) from rfl ] ; simp +arith +decide [ ih ] ;
      rw [ show verina_advanced_5.listToNat ( d1 :: t1 ) = d1 + 10 * verina_advanced_5.listToNat t1 from rfl, show verina_advanced_5.listToNat ( d2 :: t2 ) = d2 + 10 * verina_advanced_5.listToNat t2 from rfl ] ; linarith [ Nat.mod_add_div ( d1 + d2 + carry ) 10 ]
/-
The digits of the result of addAux are all less than 10, given the inputs are.
-/
theorem addAux_digits_lt_10 (l1 l2 : List Nat) (carry : Nat)
  (hl1 : ∀ d ∈ l1, d < 10) (hl2 : ∀ d ∈ l2, d < 10) (hcarry : carry < 10) :
  ∀ d ∈ verina_advanced_5.addTwoNumbers.addAux l1 l2 carry, d < 10 := by
    intro d hd;
    induction' l1 with d1 l1 ih generalizing l2 carry <;> induction' l2 with d2 l2 ih' generalizing carry <;> simp_all +arith +decide;
    · unfold verina_advanced_5.addTwoNumbers.addAux at hd; aesop;
    · unfold verina_advanced_5.addTwoNumbers.addAux at hd;
      grind;
    · -- By definition of `addAux`, when the second list is empty, the result is the first list with the carry added to the first element.
      have h_addAux_empty : verina_advanced_5.addTwoNumbers.addAux (d1 :: l1) [] carry = (d1 + carry) % 10 :: verina_advanced_5.addTwoNumbers.addAux l1 [] ((d1 + carry) / 10) := by
        -- By definition of `addAux`, when the second list is empty, the result is the first list with the carry added to the first element. Therefore, the equality holds by definition.
        rw [verina_advanced_5.addTwoNumbers.addAux];
      grind;
    · -- By definition of `addAux`, we know that `d` is either the last digit of `d1 + d2 + carry` or the result of `addAux l1 l2 (d1 + d2 + carry) / 10`.
      have h_cases : d = (d1 + d2 + carry) % 10 ∨ d ∈ verina_advanced_5.addTwoNumbers.addAux l1 l2 ((d1 + d2 + carry) / 10) := by
        unfold verina_advanced_5.addTwoNumbers.addAux at hd; aesop;
      exact h_cases.elim ( fun h => h.symm ▸ Nat.le_of_lt_succ ( Nat.mod_lt _ ( by decide ) ) ) fun h => ih _ _ hl2.2 ( Nat.div_le_of_le_mul <| by linarith ) h

/-
addAux returns a non-empty list unless inputs are empty and carry is 0.
-/
theorem addAux_nonEmpty (l1 l2 : List Nat) (carry : Nat)
  (h : l1 ≠ [] ∨ l2 ≠ [] ∨ carry ≠ 0) :
  verina_advanced_5.addTwoNumbers.addAux l1 l2 carry ≠ [] := by
    --codetic成功证明
    sorry

/-
If listToNat is 0, all elements are 0.
-/
theorem listToNat_zero_implies_forall_zero (l : List Nat) :
  verina_advanced_5.listToNat l = 0 → ∀ d ∈ l, d = 0 := by
    --codetic?成功证明
    sorry

/-
Definition of TailValid and a theorem that it propagates to the tail.
-/
def TailValid (l : List Nat) : Prop := l = [] ∨ l.getLast! ≠ 0

theorem TailValid_cons {h : Nat} {t : List Nat} : TailValid (h :: t) → TailValid t := by
  --codetic?成功证明
    sorry

/-
addAux returns empty list iff inputs are empty and carry is 0.
-/
theorem addAux_eq_nil_iff (l1 l2 : List Nat) (carry : Nat) :
  verina_advanced_5.addTwoNumbers.addAux l1 l2 carry = [] ↔ l1 = [] ∧ l2 = [] ∧ carry = 0 := by
    --codetic成功证明
    sorry

/-
Helper theorem: d :: tail is TailValid if tail is TailValid and (tail=[] -> d!=0).
-/
theorem TailValid_cons_cons (d : Nat) (tail : List Nat) :
  TailValid tail → (tail = [] → d ≠ 0) → TailValid (d :: tail) := by
    --codetic?成功证明
    sorry

/-
addAux [] l2 carry preserves TailValid.
-/
theorem addAux_nil_left_tail_valid (l2 : List Nat) (carry : Nat)
  (h2 : TailValid l2) (hc : carry < 10) :
  TailValid (verina_advanced_5.addTwoNumbers.addAux [] l2 carry) := by
    unfold verina_advanced_5.addTwoNumbers.addAux;
    unfold verina_advanced_5.TailValid at *;
    rcases l2 with ( _ | ⟨ x, _ | ⟨ y, l2 ⟩ ⟩ ) <;> simp_all +decide;
    · native_decide +revert;
    · unfold verina_advanced_5.addTwoNumbers.addAux; simp +decide [ * ] ;
      grind;
    · unfold verina_advanced_5.addTwoNumbers.addAux; simp_all +decide [ List.getLast? ] ;
      induction l2 generalizing x y carry <;> simp_all +decide [ List.getLast ];
      · unfold verina_advanced_5.addTwoNumbers.addAux; simp_all +decide [ List.getLast ] ;
        grind;
      · unfold verina_advanced_5.addTwoNumbers.addAux; simp_all +decide [ List.getLast ] ;
        rename_i ih
        contrapose! ih;
        use (z + (y + (x + carry) / 10) / 10) % 10;
        refine' ⟨ Nat.mod_lt _ ( by decide ), _ ⟩;
        use 0, z + ( y + ( x + carry ) / 10 ) / 10;
        codetic?

/-
addAux l1 [] carry preserves TailValid.
-/
theorem addAux_right_nil_tail_valid (l1 : List Nat) (carry : Nat)
  (h1 : TailValid l1) (hc : carry < 10) :
  TailValid (verina_advanced_5.addTwoNumbers.addAux l1 [] carry) := by
    unfold verina_advanced_5.TailValid at *;
    unfold verina_advanced_5.addTwoNumbers.addAux;
    rcases l1 with ( _ | ⟨ h1, t1 ⟩ ) <;> simp +arith +decide at *;
    · interval_cases carry <;> trivial;
    · induction t1 <;> simp_all +arith +decide [ add_comm ];
      · interval_cases carry <;> simp_all +decide [ verina_advanced_5.addTwoNumbers.addAux ];
        all_goals split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · -- By definition of `addAux`, if the last element of `l1` is non-zero, then the last element of the result is also non-zero.
        have h_last_nonzero : ∀ (l : List ℕ) (carry : ℕ), ¬l.getLast?.getD 0 = 0 → ¬(verina_advanced_5.addTwoNumbers.addAux l [] carry).getLast?.getD 0 = 0 := by
          intros l carry hl_nonzero
          induction' l with d l ih generalizing carry;
          · contradiction;
          · unfold verina_advanced_5.addTwoNumbers.addAux; simp_all +decide ;
            by_cases hl : l.getLast?.getD 0 = 0 <;> simp_all +decide;
            · cases l <;> simp_all +decide [ List.getLast? ];
              unfold verina_advanced_5.addTwoNumbers.addAux; simp_all +decide [ List.getLast ] ;
              split_ifs <;> simp_all +decide [ List.getLast ];
              omega;
            · cases l <;> simp_all +decide [ List.getLast? ];
              cases h : verina_advanced_5.addTwoNumbers.addAux ( ‹_› :: ‹_› ) [] ( ( d + carry ) / 10 ) <;> simp_all +decide [ List.getLast ];
              · specialize ih ( ( d + carry ) / 10 ) ; aesop;
              · specialize ih ( ( d + carry ) / 10 ) ; aesop;
        grind

/-
General version of addAux_nil_left_tail_valid without carry restriction.
-/
theorem addAux_nil_left_tail_valid_gen (l : List Nat) (c : Nat) (h : TailValid l) :
  TailValid (verina_advanced_5.addTwoNumbers.addAux [] l c) := by
    induction' l with l IH generalizing c;
    · -- If both lists are empty and carry is non-zero, then addAux returns [carry], and the TailValid of [carry] is true because carry is not zero.
      simp [verina_advanced_5.addTwoNumbers.addAux];
      unfold verina_advanced_5.TailValid; aesop;
    · -- By definition of addAux, we have:
      have h_addAux_def : verina_advanced_5.addTwoNumbers.addAux [] (l :: IH) c = (l + c) % 10 :: verina_advanced_5.addTwoNumbers.addAux [] IH ((l + c) / 10) := by
        -- By definition of addAux, we have the equality.
        rw [verina_advanced_5.addTwoNumbers.addAux];
      by_cases h : IH = [] <;> simp_all +decide [ verina_advanced_5.TailValid ];
      · cases ‹∀ c : ℕ, verina_advanced_5.addTwoNumbers.addAux [] [] c = [] ∨ ¬ ( verina_advanced_5.addTwoNumbers.addAux [] [] c ).getLast?.getD 0 = 0› ( ( l + c ) / 10 ) <;> simp_all +decide [ verina_advanced_5.addTwoNumbers.addAux ];
        · omega;
        · split_ifs at * <;> simp_all +decide [ List.getLast? ];
      · cases ‹∀ c : ℕ, ¬IH.getLast?.getD 0 = 0 → verina_advanced_5.addTwoNumbers.addAux [] IH c = [] ∨ ¬ ( verina_advanced_5.addTwoNumbers.addAux [] IH c ).getLast?.getD 0 = 0› ( ( l + c ) / 10 ) ( by cases IH <;> aesop ) <;> simp_all +decide [ List.getLast? ];
        · have := addAux_eq_nil_iff [] IH ( ( l + c ) / 10 ) ; aesop;
        · cases h : verina_advanced_5.addTwoNumbers.addAux [] IH ( ( l + c ) / 10 ) <;> aesop

/-
General version of addAux_right_nil_tail_valid without carry restriction.
-/
theorem addAux_right_nil_tail_valid_gen (l : List Nat) (c : Nat) (h : TailValid l) :
  TailValid (verina_advanced_5.addTwoNumbers.addAux l [] c) := by
    unfold verina_advanced_5.TailValid at *;
    -- We'll use induction on $l$ to show that the result of `addAux l [] c` is non-empty and its last element is not zero if $l$ is non-empty.
    induction' l with d l ih generalizing c;
    · cases c <;> simp +decide [ verina_advanced_5.addTwoNumbers.addAux ];
    · unfold verina_advanced_5.addTwoNumbers.addAux;
      cases h <;> simp_all +decide [ List.getLast! ];
      specialize ih ( ( d + c ) / 10 ) ; cases l <;> simp_all +decide [ List.getLast ];
      · cases h : ( d + c ) / 10 <;> simp_all +decide [ verina_advanced_5.addTwoNumbers.addAux ];
        omega;
      · cases h : verina_advanced_5.addTwoNumbers.addAux ( ‹_› :: ‹_› ) [] ( ( d + c ) / 10 ) <;> simp_all +decide [ List.getLast ];
        unfold verina_advanced_5.addTwoNumbers.addAux at h ; aesop

/-
Arithmetic helper: if sum/10 is 0 and inputs are non-zero, then sum%10 is non-zero.
-/
theorem sum_mod_nonzero (h1 h2 c : Nat) (h1_nz : h1 ≠ 0) (h2_nz : h2 ≠ 0) (h_div : (h1 + h2 + c) / 10 = 0) :
  (h1 + h2 + c) % 10 ≠ 0 := by
    --codetic?成功证明
    sorry

/-
Helper theorem for the cons-cons case of addAux_tail_valid: if the recursive result is empty, the current digit must be non-zero.
-/
theorem addAux_cons_cons_helper (h1 h2 c : Nat) (t1 t2 : List Nat)
  (h1_valid : TailValid (h1 :: t1))
  (h2_valid : TailValid (h2 :: t2))
  (h_res_nil : verina_advanced_5.addTwoNumbers.addAux t1 t2 ((h1 + h2 + c) / 10) = []) :
  (h1 + h2 + c) % 10 ≠ 0 := by
    --codetic?成功证明
    sorry

/-
addAux preserves TailValid property (general version without carry restriction).
-/
theorem addAux_tail_valid (l1 l2 : List Nat) (carry : Nat)
  (h1 : TailValid l1) (h2 : TailValid l2) :
  TailValid (verina_advanced_5.addTwoNumbers.addAux l1 l2 carry) := by
    -- codetic
    -- We proceed by induction on the length of the lists.
    -- 第一层归纳：处理第一个列表 l1
    induction l1 generalizing l2 carry with
    | nil =>
        -- 对应原代码第一个 · (l1 为空的情况)
        exact?
    | cons h1 t1 ih1 =>
        -- 对应原代码第二个 · (l1 为非空)
        -- 第二层归纳：处理第二个列表 l2
        induction l2 generalizing t1 carry with
        | nil =>
            -- 对应原代码内部第一个 · (l2 为空的情况)
            exact?
        | cons h2 t2 ih2 =>
            -- 对应原代码内部第二个 · (l2 为非空)
            unfold verina_advanced_5.addTwoNumbers.addAux
            apply TailValid_cons_cons
            · -- 这里的 ih1 是第一层归纳的假设
              -- 相当于原代码里的 ih _ _ ...
              apply ih1
              sorry--codetic?成功证明
              sorry--codetic?成功证明
            · --codetic成功证明
              sorry


/-
addAux [] l 0 returns l if digits are < 10.
-/
theorem addAux_nil_left_id (l : List Nat) (h : ∀ d ∈ l, d < 10) :
  verina_advanced_5.addTwoNumbers.addAux [] l 0 = l := by
    --codetic?成功证明
    sorry

/-
addAux (h1::t1) [0] 0 is the same as addAux (h1::t1) [] 0.
-/
theorem addAux_cons_zero_zero (h1 : Nat) (t1 : List Nat) :
  verina_advanced_5.addTwoNumbers.addAux (h1 :: t1) [0] 0 = verina_advanced_5.addTwoNumbers.addAux (h1 :: t1) [] 0 := by
  --codetic?
  simp only [verina_advanced_5.addTwoNumbers.addAux]

/-
addAux [0] l2 0 is the same as addAux [] l2 0 if l2 is not empty.
-/
theorem addAux_zero_left_eq (l2 : List Nat) (h : l2 ≠ []) :
  verina_advanced_5.addTwoNumbers.addAux [0] l2 0 = verina_advanced_5.addTwoNumbers.addAux [] l2 0 := by
  --codetic?成功证明
    sorry

/-
addAux l1 [0] 0 is the same as addAux l1 [] 0 if l1 is not empty.
-/
theorem addAux_zero_right_eq (l1 : List Nat) (h : l1 ≠ []) :
  verina_advanced_5.addTwoNumbers.addAux l1 [0] 0 = verina_advanced_5.addTwoNumbers.addAux l1 [] 0 := by
  --codetic?成功证明
    sorry

end Aristotletheorems

theorem addTwoNumbers_spec_satisfied (l1: List Nat) (l2: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    addTwoNumbers_postcond (l1) (l2) (addTwoNumbers (l1) (l2) h_precond) h_precond := by
      -- We prove the three parts of the postcondition separately.
      apply And.intro;
      · exact addAux_listToNat l1 l2 0;
      · constructor;
        · exact addAux_digits_lt_10 l1 l2 0 h_precond.2.2.1 h_precond.2.2.2.1 ( by norm_num );
        · by_cases h1 : l1 = [ 0 ] <;> by_cases h2 : l2 = [ 0 ] <;> simp_all +decide [ verina_advanced_5.addTwoNumbers ];
          · native_decide +revert;
          · -- Since l2 is not [0], we can use the fact that addAux preserves the last digit property.
            have h_last_digit : verina_advanced_5.addTwoNumbers.addAux [0] l2 0 = verina_advanced_5.addTwoNumbers.addAux [] l2 0 := by
              apply addAux_zero_left_eq;
              cases h_precond ; aesop;
            have h_last_digit : verina_advanced_5.addTwoNumbers.addAux [] l2 0 = l2 := by
              apply addAux_nil_left_id;
              exact h_precond.2.2.2.1;
            cases h_precond ; aesop;
          · have h_tail_valid : TailValid (verina_advanced_5.addTwoNumbers.addAux l1 [0] 0) := by
              have h_tail_valid : TailValid l1 := by
                unfold verina_advanced_5.TailValid; aesop;
              convert addAux_right_nil_tail_valid_gen l1 0 h_tail_valid using 1;
              exact addAux_zero_right_eq l1 ( by aesop );
            have h_nonempty : verina_advanced_5.addTwoNumbers.addAux l1 [0] 0 ≠ [] := by
              simp +zetaDelta at *;
              rw [ addAux_eq_nil_iff ] ; aesop;
            cases h_tail_valid <;> aesop;
          · have h_last_digit : verina_advanced_5.addTwoNumbers.addAux l1 l2 0 ≠ [] := by
              apply addAux_nonEmpty;
              cases l1 <;> cases l2 <;> aesop;
            have h_last_digit : TailValid (verina_advanced_5.addTwoNumbers.addAux l1 l2 0) := by
              have h_last_digit : verina_advanced_5.TailValid l1 ∧ verina_advanced_5.TailValid l2 := by
                unfold verina_advanced_5.TailValid; aesop;
              exact addAux_tail_valid _ _ _ h_last_digit.1 h_last_digit.2;
            cases h_last_digit <;> aesop

end verina_advanced_5
