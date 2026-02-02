/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6768ee99-57d6-4b22-b052-dfb294e55a65

The following was proved by Aristotle:

- theorem ifPowerOfFour_spec_satisfied (n: Nat) (h_precond : ifPowerOfFour_precond (n)) :
    ifPowerOfFour_postcond (n) (ifPowerOfFour (n) h_precond) h_precond
-/

import Mathlib


set_option maxHeartbeats 0

namespace verina_advanced_14

@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  True

def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  let rec helper (n : Nat) : Bool :=
    match n with
    | 0 =>
      false
    | Nat.succ m =>
      match m with
      | 0 =>
        true
      | Nat.succ l =>
        if (l+2)%4=0 then
          helper ((l+2)/4)
        else
          false
  helper n

@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)

theorem ifPowerOfFour_spec_satisfied (n: Nat) (h_precond : ifPowerOfFour_precond (n)) :
    ifPowerOfFour_postcond (n) (ifPowerOfFour (n) h_precond) h_precond := by
      unfold verina_advanced_14.ifPowerOfFour_postcond;
      -- By definition of `ifPowerOfFour`, we need to show that the helper function returns true if and only if n is a power of 4.
      apply Iff.intro;
      · revert n;
        intro n h_precond h;
        -- We'll use induction on the helper function to show that if it returns true, then n is a power of 4.
        have h_ind : ∀ n, (verina_advanced_14.ifPowerOfFour.helper n) = true → ∃ m, n = 4^m := by
          intro n hn
          induction' n using Nat.strong_induction_on with n ih;
          unfold verina_advanced_14.ifPowerOfFour.helper at hn; rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide;
          · exists 0;
          · obtain ⟨ m, hm ⟩ := ih _ ( by linarith [ Nat.mod_add_div ( n + 3 ) 4 ] ) hn.2; exact ⟨ m + 1, by rw [ pow_succ' ] ; linarith [ Nat.mod_add_div ( n + 3 ) 4 ] ⟩ ;
        exact h_ind n h;
      · rintro ⟨ m, rfl ⟩;
        induction m <;> simp_all +decide [ pow_succ' ];
        · native_decide +revert;
        · simp_all +decide [ verina_advanced_14.ifPowerOfFour ];
          unfold verina_advanced_14.ifPowerOfFour.helper;
          rcases k : 4 ^ _ with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.pow_succ' ];
          grind

end verina_advanced_14