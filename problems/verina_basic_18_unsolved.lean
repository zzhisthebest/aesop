-- -----Description-----
-- This task requires writing a Lean 4 method that computes the sum of the digits of a non-negative integer. The method should process each digit of the input number and return the total sum. The output is guaranteed to be a non-negative natural number.
--
-- -----Input-----
-- The input consists of:
-- n: A non-negative integer.
--
-- -----Output-----
-- The output is a natural number:
-- Returns the sum of the digits of the input integer.
--
-- -----Note-----
-- The input is assumed to be a valid non-negative integer.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp

@[reducible, simp]
def sumOfDigits_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc
    else loop (n / 10) (acc + n % 10)
  loop n 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  -- !benchmark @start postcond
  result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux
#check sumOfDigits.loop.induct
-- 累加器平移引理
theorem sumOfDigits_loop_acc (n y x: Nat) :
    sumOfDigits.loop n x+y = sumOfDigits.loop n x + y := by
  induction n, y using sumOfDigits.loop.induct generalizing x with
  | case1 acc => aesop
  | case2 n acc h_ne ih =>
    unfold sumOfDigits.loop
    simp

    --aesop

theorem sumOfDigits_spec_satisfied (n: Nat) (h_precond : sumOfDigits_precond (n)) :
    sumOfDigits_postcond (n) (sumOfDigits (n) h_precond) h_precond := by
  -- !benchmark @start proof
  simp_all only [sumOfDigits_postcond, sumOfDigits, ↓Char.isValue, Char.reduceToNat, String.toList]
  simp_all only [sumOfDigits_precond]
  apply And.intro
  · sorry
  · sorry

  -- !benchmark @end proof
--己
