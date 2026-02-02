-- -----Description-----
-- This task requires determining whether a given list of characters is a palindrome; that is, whether the sequence reads the same forward and backward.
--
-- -----Input-----
-- The input consists of:
-- • x: A list of characters (List Char). The list can be empty or non-empty.
--
-- -----Output-----
-- The output is a Boolean value (Bool):
-- • Returns true if the input list is a palindrome.
-- • Returns false otherwise.
--
-- -----Note-----
-- An empty list is considered a palindrome. The function does not impose any additional preconditions.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
namespace tmp
set_option maxHeartbeats 0
@[reducible, simp]
def IsPalindrome_precond (x : List Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false  -- This case should not occur due to valid indices
  else true
-- !benchmark @end code_aux


def IsPalindrome (x : List Char) (h_precond : IsPalindrome_precond (x)) : Bool :=
  -- !benchmark @start code
  if x.length = 0 then true else isPalindromeHelper x 0 (x.length - 1)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def IsPalindrome_postcond (x : List Char) (result: Bool) (h_precond : IsPalindrome_precond (x)) :=
  -- !benchmark @start postcond
  result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

#check isPalindromeHelper.induct
theorem IsPalindrome_spec_satisfied (x: List Char) (h_precond : IsPalindrome_precond (x)) :
    IsPalindrome_postcond (x) (IsPalindrome (x) h_precond) h_precond := by
  -- !benchmark @start proof
  --一眼典型的数学归纳法
  unfold IsPalindrome_postcond IsPalindrome
  simp
  rename List Char => a--把x重命名为a
  constructor--把<=>变成=>和<=
  · --这是一个spec
    have aux (x : Nat) : (0 ≤ x) → (x ≤ a.length) → a = [] ∨ isPalindromeHelper a x (a.length - 1-x) = true →
      ∀ (i : Nat), x<=i∧i<a.length-x → a[i]?.getD 'A' = a[a.length - i - 1]?.getD 'A'
      := by
      --codetic?
      sorry
      -- intro hx₀ hx₁
      -- let nx := a.length - x
      -- have hn₁ : nx = a.length - x := by rfl
      -- have hn₂ : x = a.length - nx := by
      --   grind
      -- rw [hn₂]
      -- have h1:0<=nx:=by grind
      -- have h2:nx<=a.length:=by grind
      -- clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      -- revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      -- induction nx with
      -- | zero=>
      --   unfold isPalindromeHelper
      --   simp

      -- | succ n1 ih=>
      --   unfold isPalindromeHelper
      --   simp
      --   intro h1 h2 i h3 h4
      --   split at h2
      --   · rename_i x1 x2 c1 c2 heq1 heq2

      --     by_cases h5:a.length - n1 ≤ i ∧ i < a.length - (a.length - n1)
      --     · apply ih
      --       --clear ih
      --       · grind
      --       · grind
      --       · --得用h2,h2的第二项a.length ≤ a.length - (n1 + 1) + (a.length - (n1 + 1)) + 1表示定义里i小于j不成立时
      --         rcases h2 with (h2 | h2 | h2)
      --         · grind
      --         · grind
      --         · grind
      --       · exact h5
      --     · --这种用不了ih
      --       have hi:i=a.length-(n1+1)∨i=n1:=by
      --         grind
      --       rcases h2 with (h2 | h2 | h2)
      --       · rcases hi with hi|hi
      --         · grind
      --         · grind
      --       · rcases hi with hi|hi
      --         · grind
      --         · grind
      --       · rcases hi with hi|hi
      --         · grind
      --         · --其实和上一个case类似，按理说grind应该能证明，但它没证明
      --           have h6:a.length - 1 - (a.length - (n1 + 1))=n1:=by grind
      --           grind
      --   · rename_i x1 x2 h_c1c2
      --     by_cases h5:a.length - n1 ≤ i ∧ i < a.length - (a.length - n1)
      --     · apply ih
      --       --clear ih
      --       · grind
      --       · grind
      --       · --得用h2,h2的第二项a.length ≤ a.length - (n1 + 1) + (a.length - (n1 + 1)) + 1表示定义里i小于j不成立时
      --         rcases h2 with (h2 | h2 | h2)
      --         · grind
      --         · grind
      --         · grind
      --       · exact h5
      --     · --这种用不了ih
      --       have hi:i=a.length-(n1+1)∨i=n1:=by
      --         grind
      --       rcases h2 with (h2 | h2 | h2)
      --       · rcases hi with hi|hi
      --         · grind
      --         · grind
      --       · rcases hi with hi|hi
      --         · simp_all
      --           grind
      --         · simp_all
      --           grind
      --       · rcases hi with hi|hi
      --         · grind
      --         · grind
    --codetic
    sorry

  · --这是一个spec
    have aux (x : Nat) : (0 ≤ x) → (x ≤ a.length)  →
      (∀ (i : Nat), x<=i∧i<a.length-x → a[i]?.getD 'A' = a[a.length - i - 1]?.getD 'A')→ a = [] ∨ isPalindromeHelper a x (a.length - 1-x) = true
      := by
      --codetic
      -- induction x,(a.length - 1 - x) using isPalindromeHelper.induct a
      -- unfold isPalindromeHelper
      -- sorry
      -- --codetic
      -- unfold isPalindromeHelper
      -- sorry
      -- --codetic
      -- unfold isPalindromeHelper
      -- --codetic
      intro hx₀ hx₁
      let nx := a.length - x
      have hn₁ : nx = a.length - x := by rfl
      have hn₂ : x = a.length - nx := by
        grind
      rw [hn₂]
      have h1:0<=nx:=by grind
      have h2:nx<=a.length:=by grind
      clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      induction nx with
      | zero=>
        unfold isPalindromeHelper
        simp

      | succ n1 ih=>
        unfold isPalindromeHelper
        intro h1 h2 h3
        split
        split
        split
        · simp
          rename_i x1 x2 c1 c2 heq1 heq2 hueq
          rename_i h4
          --用反证法
          have h5:a[a.length - (n1 + 1)]?.getD 'A' = a[a.length - (a.length - (n1 + 1)) - 1]?.getD 'A':=by
            apply h3
            constructor
            simp
            apply lt_of_lt_of_le h4
            simp
          grind
        · rename_i x1 x2 c1 c2 heq1 heq2 hueq
          rename_i h4
          have h5:a.length - (n1 + 1) + 1=a.length - n1:=by
            omega

          have h6:a.length - 1 - (a.length - (n1 + 1)) - 1=a.length - 1 - (a.length - n1):=by
            omega
          rw [h5,h6]
          apply ih
          simp
          grind
          intro i h7
          have h8:a.length - (n1 + 1) ≤ i ∧ i < a.length - (a.length - (n1 + 1)):=by
            omega
          apply h3
          exact h8
        · simp
          rename_i x1 x2 h_c1c2
          --simp at h_c1c2
          --codetic
          --grind
          by_contra
          revert h_c1c2
          simp
          clear ih h1 h3--为了让grind不达到heartbeats极限，所以去掉无关的假设
          constructor
          exact ⟨a[a.length - (n1 + 1)], by grind⟩
          exact ⟨a[a.length - 1 - (a.length - (n1 + 1))], by grind⟩
        · simp

    intro a_1
    simp_all only [IsPalindrome_precond, Nat.zero_le, ↓Char.isValue, and_imp, forall_const, getElem?_pos,
      Option.getD_some]
    grind

#check
--己。这个真不容易啊。本质和68一样
