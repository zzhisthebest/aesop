-- -----Description-----  
-- The problem involves finding the first occurrence of a specified key in an array of integers. Your task is to identify the index at which the key appears for the first time in the array and return that index. If the key is not found, return -1.
--
-- -----Input-----  
-- The input consists of:  
-- • a: An array of integers.  
-- • key: An integer representing the value to search for in the array.
--
-- -----Output-----  
-- The output is an integer which represents:  
-- • The index in the array where the key is found, provided that the index is in the range [0, a.size).  
-- • -1 if the key is not present in the array.  
-- In addition, if the output is not -1, then a[(Int.toNat result)]! equals key and every element in the array prior to this index is not equal to key.
--
-- -----Note-----  
-- The function performs a linear search beginning at index 0 and returns the first occurrence of the key. There are no additional preconditions on the input array; it can be empty or non-empty.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Find_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  -- !benchmark @start code
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  -- !benchmark @start postcond
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Find_spec_satisfied (a: Array Int) (key: Int) (h_precond : Find_precond (a) (key)) :
    Find_postcond (a) (key) (Find (a) (key) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

