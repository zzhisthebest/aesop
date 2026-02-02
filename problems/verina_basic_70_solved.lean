-- -----Description-----
-- This task involves determining the first index in an array where a given condition holds true. The goal is to identify the position of the first element that meets a specified criterion, ensuring that no preceding element does.
--
-- -----Input-----
-- The input consists of:
-- • a: An array of elements (for testing purposes, you can assume it is an array of integers).
-- • P: A predicate function on the elements (represented as a string for test cases, e.g., "fun x => x > 5"). It is assumed that at least one element in the array satisfies P.
--
-- -----Output-----
-- The output is a natural number (Nat) which represents the index of the first element in the array that satisfies the predicate P.
-- • The index returned is less than the size of the array.
-- • The element at the returned index satisfies P.
-- • All elements before the returned index do not satisfy P.
--
-- -----Note-----
-- It is assumed that the array contains at least one element that satisfies P. In cases where this precondition does not hold, the behavior of the function is not guaranteed by the specification.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Codetic
set_option maxHeartbeats 0
set_option trace.codetic true
namespace tmp

@[reducible, simp]
def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ P (a[i]!)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if P (a[n]!) then n else loop (n + 1)
    else--这个分支永远不会抵达
      0
  loop 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LinearSearch3_postcond (a : Array Int) (P : Int -> Bool) (result: Nat) (h_precond : LinearSearch3_precond (a) (P)) :=
  -- !benchmark @start postcond
  result < a.size ∧ P (a[result]!) ∧ (∀ k, k < result → ¬ P (a[k]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

--和basic_68一个套路,不同点是precond导致在证明第二个spec时aux要更复杂
theorem LinearSearch3_spec_satisfied (a: Array Int) (P: Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    LinearSearch3_postcond (a) (P) (LinearSearch3 (a) (P) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold LinearSearch3_postcond LinearSearch3
  constructor
  · --这是一个spec
    have aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → LinearSearch3.loop a P x < a.size := by
      codetic
      -- intro hx₀ hx₁
      -- let nx := a.size - x
      -- have hn₁ : nx = a.size - x := by rfl
      -- have hn₂ : x = a.size - nx := by
      --   grind
      -- rw [hn₂]
      -- have h1:0<=nx:=by grind
      -- have h2:nx<=a.size:=by grind
      -- clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      -- revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      -- induction nx with
      -- | zero=>
      --   unfold LinearSearch3.loop
      --   simp
      --   grind--grind自动使用precond

      -- | succ n1 ih=>
      --   unfold LinearSearch3.loop
      --   intro h1 h2
      --   split_ifs
      --   · assumption
      --   · grind
      --   · grind
    apply aux 0 (by simp) (by grind)

  constructor
  · --这是一个spec
    unfold LinearSearch3_precond at h_precond
    have aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → (∀ i < x, ¬P a[i]!) → P a[LinearSearch3.loop a P x]! = true:= by
      codetic
      -- intro hx₀ hx₁
      -- let nx := a.size - x
      -- have hn₁ : nx = a.size - x := by rfl
      -- have hn₂ : x = a.size - nx := by
      --   grind
      -- rw [hn₂]
      -- have h1:0<=nx:=by grind
      -- have h2:nx<=a.size:=by grind
      -- clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      -- revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      -- induction nx with
      -- | zero=>
      --   unfold LinearSearch3.loop
      --   simp--此时goal其实是false->xxx
      --   grind

      -- | succ n1 ih=>
      --   unfold LinearSearch3.loop
      --   simp
      --   intro h1
      --   split_ifs
      --   · grind
      --   · grind
      --   · grind
    grind
  · --这是一个spec
    have aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → (∀ i, x ≤ i → i < LinearSearch3.loop a P x → ¬P a[i]!) := by
      codetic
      -- intro hx₀ hx₁
      -- let nx := a.size - x
      -- have hn₁ : nx = a.size - x := by rfl
      -- have hn₂ : x = a.size - nx := by
      --   grind
      -- rw [hn₂]
      -- have h1:0<=nx:=by grind
      -- have h2:nx<=a.size:=by grind
      -- clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      -- revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      -- induction nx with
      -- | zero=>
      --   unfold LinearSearch3.loop
      --   simp

      -- | succ n1 ih=>
      --   unfold LinearSearch3.loop
      --   simp
      --   split
      --   split
      --   · grind
      --   · intro h1
      --     grind
      --   · grind
    intro k h1
    apply aux 0 (by simp) (by simp)
    simp
    assumption

  -- !benchmark @end proof
--己。
