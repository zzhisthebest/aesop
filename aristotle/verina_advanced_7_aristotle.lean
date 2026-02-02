/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c71b6244-d1eb-42ce-8151-9b646169c06c

The following was proved by Aristotle:

- theorem binaryToDecimal_spec_satisfied (digits: List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    binaryToDecimal_postcond (digits) (binaryToDecimal (digits) h_precond) h_precond

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib
import Codetic

set_option maxHeartbeats 0

namespace verina_advanced_7

@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)

def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  let rec helper (digits : List Nat) : Nat :=
    match digits with
    | [] => 0
    | first :: rest => first * Nat.pow 2 rest.length + helper rest
  helper digits

@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0

theorem binaryToDecimal_spec_satisfied (digits: List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    binaryToDecimal_postcond (digits) (binaryToDecimal (digits) h_precond) h_precond := by
      -- By definition of `binaryToDecimal`, we can rewrite the goal using the recursive definition.
      have h_rec : ∀ (digits : List ℕ), (∀ d ∈ digits, d = 0 ∨ d = 1) → verina_advanced_7.binaryToDecimal.helper digits = List.foldl (fun acc bit => acc * 2 + bit) 0 digits := by
        intro digits h_precond
        induction' digits with d digits ih
        all_goals generalize_proofs at *;
        · rfl;
        · simp +decide [ verina_advanced_7.binaryToDecimal.helper ];
          rw [ ih fun x hx => h_precond x ( List.mem_cons_of_mem _ hx ) ];
          clear ih h_precond;
          simp_all only [binaryToDecimal_precond, Bool.decide_or, List.all_eq_true, Bool.or_eq_true,
            decide_eq_true_eq]
          induction digits using List.reverse_RecOn with
          | nil => simp_all only [List.length_nil, pow_zero, mul_one, List.foldl_nil, add_zero]
          | append_singleton l a
            ih =>
            simp_all only [List.length_append, List.length_cons, List.length_nil, zero_add, List.foldl_append,
              List.foldl_cons, List.foldl_nil]
            grind
      unfold verina_advanced_7.binaryToDecimal; aesop;

end verina_advanced_7
