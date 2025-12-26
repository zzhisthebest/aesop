-- -----Description-----
-- Given two integers, the task is to compute two output values: one being the sum of the integers and the other being their difference.
--
-- -----Input-----
-- The input consists of two integers:
-- • x: An integer.
-- • y: An integer.
--
-- -----Output-----
-- The output is a tuple of two integers:
-- • The first element is x + y.
-- • The second element is x - y.
--
-- -----Note-----
-- It is assumed that x and y are valid integers. There are no additional constraints on the inputs.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  -- !benchmark @start code
  let more := x + y
  let less := x - y
  (more, less)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def MultipleReturns_postcond (x : Int) (y : Int) (result: (Int × Int)) (h_precond : MultipleReturns_precond (x) (y)) :=
  -- !benchmark @start postcond
  result.1 = x + y ∧ result.2 + y = x
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem MultipleReturns_spec_satisfied (x: Int) (y: Int) (h_precond : MultipleReturns_precond (x) (y)) :
    MultipleReturns_postcond (x) (y) (MultipleReturns (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold MultipleReturns_postcond MultipleReturns
  simp
  -- !benchmark @end proof
--己。
