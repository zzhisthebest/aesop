-- -----Description-----
-- This problem involves determining the index of the first occurrence of a specified element within an array of integers. The objective is to identify the correct position where the target element appears for the first time, ensuring that all elements prior to that index are different from the target.
--
-- -----Input-----
-- The input consists of:
-- • a: An array of integers.
-- • e: An integer representing the element to search for.
--
-- -----Output-----
-- The output is a natural number (Nat) representing the index of the first occurrence of e in the array.
-- • If the element e exists in the array, the index n will satisfy the conditions specified above.
--
-- -----Note-----
-- It is assumed that the input satisfies the precondition where at least one index i in a exists such that a[i]! = e.
-- The implementation uses a helper function to iterate through the array recursively.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Mathlib

@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ a[i]! = e
  -- !benchmark @end precond


-- !benchmark @start code_aux
def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0
-- !benchmark @end code_aux


def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  -- !benchmark @start code
  linearSearchAux a e 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  -- !benchmark @start postcond
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

--和basic_68和70一个套路
theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold LinearSearch_postcond LinearSearch
  unfold LinearSearch_precond at h_precond
  constructor
  · --这是一个spec
    have aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → linearSearchAux a e x < a.size := by
      intro hx₀ hx₁
      let nx := a.size - x
      have hn₁ : nx = a.size - x := by rfl
      have hn₂ : x = a.size - nx := by
        grind
      rw [hn₂]
      have h1:0<=nx:=by grind
      have h2:nx<=a.size:=by grind
      clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      induction nx with
      | zero=>
        unfold linearSearchAux
        simp
        grind--grind自动使用precond

      | succ n1 ih=>
        unfold linearSearchAux
        intro h1 h2
        split_ifs
        · assumption
        · grind
        · grind
    apply aux 0 (by simp) (by grind)
  constructor
  · have aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → (∀ i < x, ¬ a[i]! =e) → a[linearSearchAux a e x]! = e:= by
      intro hx₀ hx₁
      let nx := a.size - x
      have hn₁ : nx = a.size - x := by rfl
      have hn₂ : x = a.size - nx := by
        grind
      rw [hn₂]
      have h1:0<=nx:=by grind
      have h2:nx<=a.size:=by grind
      clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
      revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
      induction nx with
      | zero=>
        unfold linearSearchAux
        simp--此时goal其实是false->xxx
        grind

      | succ n1 ih=>
        unfold linearSearchAux
        simp
        intro h1
        split_ifs
        · grind
        · grind
        · grind
    grind

  · --这是一个spec
    have aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → (∀ i, x ≤ i → i < linearSearchAux a e x → a[i]! ≠ e) := by
        intro hx₀ hx₁
        let nx := a.size - x
        have hn₁ : nx = a.size - x := by rfl
        have hn₂ : x = a.size - nx := by
          grind
        rw [hn₂]
        have h1:0<=nx:=by grind
        have h2:nx<=a.size:=by grind
        clear hx₀ hx₁ hn₁ hn₂--这些hyp没用了
        revert h2 h1--因为nx是有范围的，如果不加这一句，就变成在[0,+无穷]归纳了，这显然不是等价变换
        induction nx with
      | zero=>
        unfold linearSearchAux
        simp

      | succ n1 ih=>
        unfold linearSearchAux
        simp
        split
        split
        · grind
        · intro h1
          grind
        · grind
    intro i
    apply aux
    simp
    grind
    grind
  -- !benchmark @end proof
--己
