/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ec505fdf-5bbf-4d85-b47d-f99515685785

The following was proved by Aristotle:

- theorem countSumDivisibleBy_spec_satisfied (n: Nat) (d: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    countSumDivisibleBy_postcond (n) (d) (countSumDivisibleBy (n) (d) h_precond) h_precond
-/
import Mathlib
import Codetic


set_option maxHeartbeats 0

namespace verina_advanced_9

def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0

@[reducible]
def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  d > 0

def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0

def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  let rec go (i acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i'+1 =>
      let acc' := if isSumDivisibleBy i' d then acc + 1 else acc
      go i' acc'
  go n 0

@[reducible]
def countSumDivisibleBy_postcond (n : Nat) (d : Nat) (result: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Prop :=
  (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n))) - result = 0 ∧
  result ≤ (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)))

theorem countSumDivisibleBy_spec_satisfied (n: Nat) (d: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    countSumDivisibleBy_postcond (n) (d) (countSumDivisibleBy (n) (d) h_precond) h_precond := by
      -- Let's simplify the goal using the definition of `countSumDivisibleBy`.
      unfold verina_advanced_9.countSumDivisibleBy;
      -- Let's simplify the goal using the definition of `countSumDivisibleBy.go`.
      have h_simp : ∀ (i acc : ℕ), verina_advanced_9.countSumDivisibleBy.go d i acc = acc + List.length (List.filter (fun x => isSumDivisibleBy x d) (List.range i)) := by
        -- We'll use induction on $i$ to prove the equality.
        intro i acc
        induction' i with i ih generalizing acc;
        · exact?;
        · simp_all +decide [ List.range_succ ];
          rw [ verina_advanced_9.countSumDivisibleBy.go ];
          grind;
      -- By definition of `countSumDivisibleBy_postcond`, we need to show that the length of the filtered list is equal to the countSumDivisibleBy result and that the count is less than or equal to the length.
      simp [verina_advanced_9.countSumDivisibleBy_postcond, h_simp];
      rw [ List.filter_congr ] ; aesop;
      exact fun x hx => by rw [ List.mem_range ] at hx; aesop;

end verina_advanced_9
