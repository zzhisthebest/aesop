import Lean
namespace tmp


-- !benchmark @start code_aux
def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s
-- !benchmark @end code_aux


def double_array_elements (s : Array Int)  : Array Int :=
  double_array_elements_aux s s 0

#check double_array_elements_aux.induct

open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta
elab "parseInduct" : tactic => do
  let env ← getEnv
  env.constants.forM fun name _ => do
    logInfo s!"Constant: {name}"

elab "funInduct" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- #check tmp.double_array_elements_aux.induct
  -- Locate a call to double_array_elements_aux in the goal
  let some call := goalType.find? (fun e =>
    match e.getAppFn with
    | .const `tmp.double_array_elements_aux _ => true
    | _ => false
  ) | throwError "No double_array_elements_aux call found"

  let args := call.getAppArgs
  if args.size != 3 then throwError "Expected 3 arguments"

  -- Extract arguments
  let arg0 := args[0]!  -- s_old (fixed parameter)
  let arg1 := args[1]!  -- s (induction parameter)
  let arg2 := args[2]!  -- j (induction parameter)

  if !arg0.isFVar || !arg1.isFVar || !arg2.isFVar then
    throwError "Arguments must be fvars"

  goal.withContext do
    let name0 ← arg0.fvarId!.getUserName
    let name1 ← arg1.fvarId!.getUserName
    let name2 ← arg2.fvarId!.getUserName

    -- Experiment: flexibly handle an arbitrary number of fixed
    -- parameters and induction parameters
    let fixedNames : Array Name := #[name0]          -- list of fixed parameters
    let inductNames : Array Name := #[name1, name2] -- list of induction parameters
    let inductIdent := mkIdent `tmp.double_array_elements_aux.induct

    -- Approach: dynamically construct and parse a tactic string
    -- (most flexible, can handle arbitrary arity)
    let inductStr := String.intercalate ", " (inductNames.map toString).toList
    let fixedStr := String.intercalate " " (fixedNames.map toString).toList
    let tacticStr := s!"induction {inductStr} using {inductIdent.getId} {fixedStr}"

    -- Parse the tactic string using the tactic parser
    let env ← getEnv
    let parserFn := Parser.runParserCategory env `tactic tacticStr
    match parserFn with
    | Except.ok stx => evalTactic stx
    | Except.error err => throwError "Failed to parse tactic: {err}"

example : 1 + 1 = 2 := by
  parseInduct

end tmp
