import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def only_once_precond (a : Array Int) (key : Int) : Prop :=
  True

def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1

def only_once (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) : Bool :=
  only_once_loop a key 0 0

def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0

@[reducible, simp]
def only_once_postcond (a : Array Int) (key : Int) (result: Bool) (h_precond : only_once_precond (a) (key)) :=
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)


theorem only_once_loop_step (a : Array Int) (key : Int) (i keyCount : Nat)
    (h : i < a.size) :
    only_once_loop a key i keyCount =
      let newCount :=
        if a[i] = key then keyCount + 1 else keyCount
      only_once_loop a key (i+1) newCount:= by 
aesop


end tmp