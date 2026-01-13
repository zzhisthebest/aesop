module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_14917
public def only_once_precond (a : Array Int) (key : Int) : Prop :=
  True

public def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1

public def only_once (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) : Bool :=
  only_once_loop a key 0 0

public def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0

public def only_once_postcond (a : Array Int) (key : Int) (result: Bool) (h_precond : only_once_precond (a) (key)) :=
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)


public theorem drop_succ_eq (a : Array Int) (i : Nat) (h : i < a.size) :
    a.drop (i+1) = (a.drop i).drop 1:= by 
sorry


end tmp_lemma_14917