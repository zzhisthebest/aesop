/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 49f730d1-a3d6-47ad-87b1-1d68fd3cdc9f

The following was proved by Aristotle:

- theorem findMajorityElement_spec_satisfied (lst: List Int) (h_precond : findMajorityElement_precond (lst)) :
    findMajorityElement_postcond (lst) (findMajorityElement (lst) h_precond) h_precond
-/

import Mathlib
import Codetic

set_option maxHeartbeats 0

namespace verina_advanced_11

@[reducible, simp]
def findMajorityElement_precond (lst : List Int) : Prop :=
  True

def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0

def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  let n := lst.length
  let majority := lst.find? (fun x => countOccurrences x lst > n / 2)
  match majority with
  | some x => x
  | none => -1

@[reducible, simp]
def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

theorem findMajorityElement_spec_satisfied (lst: List Int) (h_precond : findMajorityElement_precond (lst)) :
    findMajorityElement_postcond (lst) (findMajorityElement (lst) h_precond) h_precond := by
      simp +decide [ verina_advanced_11.findMajorityElement ];
      cases h : List.find? ( fun x => Decidable.decide ( lst.length / 2 < verina_advanced_11.countOccurrences x lst ) ) lst <;> simp_all +decide [ List.filter_eq ];
      · -- Since `countOccurrences` is equivalent to `List.count`, we can directly apply `h` to conclude the proof.
        left; exact (by
        -- Since the count in the list is the same as the count in the list when considering the foldl operation, we can conclude that the count in the list is ≤ n/2 for any x in the list.
        convert h using 1;
        unfold verina_advanced_11.countOccurrences;
        congr! 3;
        ext; codetic?);
      · -- By definition of `find?`, if `find? (fun x => lst.length / 2 < countOccurrences x lst) lst = some x`, then `x` is in the list and satisfies the condition.
        have h_find : ∀ x ∈ lst, (lst.length / 2 < verina_advanced_11.countOccurrences x lst) → (lst.length / 2 < List.count x lst) := by
          intro x hx h; convert h using 1;
          -- By definition of `countOccurrences`, we have `countOccurrences x lst = List.count x lst`.
          simp [verina_advanced_11.countOccurrences];
          clear h hx ‹List.find? ( fun x => Decidable.decide ( lst.length / 2 < verina_advanced_11.countOccurrences x lst ) ) lst = Option.some _›;
          codetic?
        -- By definition of `find?`, if `find? (fun x => lst.length / 2 < countOccurrences x lst) lst = some x`, then `x` is in the list and satisfies the condition. Therefore, we can conclude that `x` is the majority element.
        have h_majority : ∀ x ∈ lst, (lst.length / 2 < verina_advanced_11.countOccurrences x lst) → (∀ y ∈ lst, List.count y lst ≤ lst.length / 2 ∨ y = x) := by
          intros x hx hx' y hy
          by_contra h_contra
          push_neg at h_contra
          have h_count : List.count x lst + List.count y lst ≤ lst.length := by
            have h_count : ∀ l : List ℤ, x ≠ y → List.count x l + List.count y l ≤ l.length := by
              codetic?--induction
            exact h_count lst ( Ne.symm h_contra.2 );
          linarith [ h_find x hx hx', Nat.div_add_mod ( List.length lst ) 2, Nat.mod_lt ( List.length lst ) two_pos ];
        codetic?

end verina_advanced_11
