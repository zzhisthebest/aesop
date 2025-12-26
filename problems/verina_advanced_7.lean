-- -----Description-----
-- This task requires writing a Lean 4 function that converts a binary number represented as a list of digits (0 or 1) into its corresponding decimal value. The list is ordered in big-endian format, meaning the most significant digit comes first.
-- The function should interpret the list as a binary number and return its decimal representation as a natural number.
--
-- -----Input-----
-- The input is a list of natural numbers:
-- digits: A list of digits, each of which is either 0 or 1, representing a binary number in big-endian order.
--
-- -----Output-----
-- The output is a natural number:
-- Returns the decimal value of the binary number represented by the input list.
--
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  -- !benchmark @start precond
  digits.all (fun d => d = 0 ∨ d = 1)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  -- !benchmark @start code
  let rec helper (digits : List Nat) : Nat :=
    match digits with
    | [] => 0
    | first :: rest => first * Nat.pow 2 rest.length + helper rest
  helper digits
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  -- !benchmark @start postcond
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem binaryToDecimal_spec_satisfied (digits: List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    binaryToDecimal_postcond (digits) (binaryToDecimal (digits) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

