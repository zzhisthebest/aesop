-- -----Description-----
-- This task requires writing a Lean 4 method that computes the product of the first even and the first odd number encountered in a list of integers. The method should search the list for the earliest even number and the earliest odd number, then return the product of these two numbers.
--
-- -----Input-----
-- The input consists of:
-- lst: A list of integers.
--
-- -----Output-----
-- The output is an integer:
-- Returns the product resulting from multiplying the first even number and the first odd number found in the list.
--
-- -----Note-----
-- The input list is assumed to contain at least one even number and one odd number.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven--竟然还有findIdx这样方便的函数
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findProduct_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  -- !benchmark @start code
  match firstEvenOddIndices lst with
  | some (ei, oi) => lst[ei]! * lst[oi]!
  | none => 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  -- !benchmark @start postcond
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findProduct_spec_satisfied (lst: List Int) (h_precond : findProduct_precond (lst)) :
    findProduct_postcond (lst) (findProduct (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findProduct findProduct_postcond
  split
  case h_1 _ ei oi _ =>--case tag x₁ ... xₙ => tac additionally renames the n most recent hypotheses with inaccessible names to the given names.
    split
    case h_1 _ ei' oi' heq =>
      grind
      -- have : ei = ei' ∧ oi = oi' := by
      --   rw [Option.some_inj] at heq
      --   cases heq with
      --   | refl => exact ⟨rfl, rfl⟩
      -- simp [this]
    case h_2 _ heq => contradiction--heq不成立
  case h_2 => simp
  -- !benchmark @end proof
--己。
