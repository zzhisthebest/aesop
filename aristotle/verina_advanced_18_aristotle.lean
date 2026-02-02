/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b024c90a-3fb9-4ea0-983e-0f170fcbfb93

The following was proved by Aristotle:

- theorem isArmstrong_spec_satisfied (n: Nat) (h_precond : isArmstrong_precond (n)) :
    isArmstrong_postcond (n) (isArmstrong (n) h_precond) h_precond
-/

import Mathlib
import Codetic

set_option maxHeartbeats 0

namespace verina_advanced_18

def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  True

def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0

def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  let k := countDigits n
  sumPowers n k = n

@[reducible]
def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))

noncomputable section AristotleLemmas

/-
sumPowers n k is equal to the sum of the k-th powers of the digits of n.
-/
theorem verina_advanced_18.sumPowers_eq_digits_sum (n k : Nat) :
  verina_advanced_18.sumPowers n k = List.sum ((Nat.digits 10 n).map (fun d => d ^ k)) := by
    conv_lhs => rw [ verina_advanced_18.sumPowers ] ;
    -- We'll use induction on $n$ to prove that the go function correctly sums the digits raised to the power $k$.
    have h_ind : ∀ n acc, verina_advanced_18.sumPowers.go k n acc = acc + List.sum (List.map (fun d => d ^ k) (Nat.digits 10 n)) := by
      intro n acc; induction' n using Nat.strong_induction_on with n ih generalizing acc; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod, Nat.div_add_mod ] ;
      · unfold verina_advanced_18.sumPowers.go; codetic?
      · unfold verina_advanced_18.sumPowers.go; codetic?
      · unfold verina_advanced_18.sumPowers.go; codetic?
    codetic?

/-
Helper lemma: `Nat.toDigitsCore` produces the reverse of `Nat.digits` (mapped to chars) for positive `n`.
-/
theorem verina_advanced_18.toDigitsCore_eq_digits_reverse (n fuel : Nat) (acc : List Char)
    (h_fuel : n < fuel) (h_pos : 0 < n) :
    (Nat.toDigitsCore 10 fuel n acc).map (fun c => c.toNat - 48) =
    (Nat.digits 10 n).reverse ++ acc.map (fun c => c.toNat - 48) := by
      induction' fuel with fuel ih generalizing n acc <;> simp_all +decide [ Nat.toDigitsCore ];
      split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · interval_cases n <;> trivial;
      · rw [ ih ( n / 10 ) _ ( by omega ) ( by omega ) ] ; simp +arith +decide [ List.map ] ;
        have := Nat.mod_lt n ( by decide : 0 < 10 ) ; interval_cases n % 10 <;> trivial;

/-
The list of digits from `toString n` corresponds to `[0]` if `n=0`, and the reverse of `Nat.digits 10 n` otherwise.
-/
theorem verina_advanced_18.digits_from_string_eq_digits_reverse_if (n : Nat) :
  List.map (fun c => c.toNat - 48) (toString n).toList =
  if n = 0 then [0] else (Nat.digits 10 n).reverse := by

    cases n <;> simp_all +decide [ ToString.toString ];
    -- Apply the lemma `verina_advanced_18.toDigitsCore_eq_digits_reverse` with `fuel = n + 2` and `acc = []`.
    have h_digits : (Nat.toDigitsCore 10 (Nat.succ ‹_› + 1) (Nat.succ ‹_›) []).map (fun c => c.toNat - 48) = (Nat.digits 10 (Nat.succ ‹_›)).reverse ++ [] := by
      exact verina_advanced_18.toDigitsCore_eq_digits_reverse _ _ _ ( Nat.lt_succ_self _ ) ( Nat.succ_pos _ );
    unfold Nat.repr; codetic?

end AristotleLemmas

theorem isArmstrong_spec_satisfied (n: Nat) (h_precond : isArmstrong_precond (n)) :
    isArmstrong_postcond (n) (isArmstrong (n) h_precond) h_precond := by
      unfold verina_advanced_18.isArmstrong_postcond verina_advanced_18.isArmstrong;
      -- By definition of `digits_from_string_eq_digits_reverse_if`, we can rewrite `n'` in terms of the digits of `n`.
      have hn'_eq_sumPowers : List.foldl (fun (acc d : ℕ) => acc + d ^ verina_advanced_18.countDigits n) 0 ((Nat.digits 10 n).reverse.map (fun d => d)) = verina_advanced_18.sumPowers n (verina_advanced_18.countDigits n) := by
        rw [ verina_advanced_18.sumPowers_eq_digits_sum ];
        induction ( Nat.digits 10 n ) <;> codetic?;
      -- By definition of `digits_from_string_eq_digits_reverse_if`, we can rewrite `n'` in terms of the digits of `n` and simplify.
      have hn'_eq_sumPowers_simplified : List.foldl (fun (acc d : ℕ) => acc + d ^ verina_advanced_18.countDigits n) 0 ((Nat.digits 10 n).reverse.map (fun d => d)) = List.foldl (fun (acc d : ℕ) => acc + d ^ verina_advanced_18.countDigits n) 0 ((toString n).toList.map (fun c => c.toNat - 48)) := by
        rw [ verina_advanced_18.digits_from_string_eq_digits_reverse_if ];
        cases n <;> simp +decide;
        native_decide +revert;
      grind +ring

end verina_advanced_18
example:1+1=2:=by
  unfold Nat.repr
#check Nat.digits_of_two_le_of_pos
