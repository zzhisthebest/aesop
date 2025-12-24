import Aesop
set_option maxHeartbeats 0
namespace tmp
def absDiff (a b : Float) : Float :=
  if a - b < 0.0 then b - a else a - b

@[reducible, simp]
def has_close_elements_precond (numbers : List Float) (threshold : Float) : Prop :=
  threshold ≥ 0.0

def has_close_elements (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) : Bool :=
  let len := numbers.length
  let rec outer (idx : Nat) : Bool :=
    if idx < len then
      let rec inner (idx2 : Nat) : Bool :=
        if idx2 < idx then
          let a := numbers.getD idx2 0.0
          let b := numbers.getD idx 0.0
          let d := absDiff a b
          if d < threshold then true else inner (idx2 + 1)
        else
          false
      if inner 0 then true else outer (idx + 1)
    else
      false
  outer 0

@[reducible, simp]
def has_close_elements_postcond (numbers : List Float) (threshold : Float) (result: Bool) (h_precond : has_close_elements_precond (numbers) (threshold)) :=
  ¬ result ↔ (List.Pairwise (fun a b => absDiff a b ≥ threshold) numbers)


theorem not_exists_close_iff_pairwise
    (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond numbers threshold) :
    (¬ ∃ i j, i < j ∧ i < numbers.length ∧ j < numbers.length ∧
        absDiff (numbers.getD i 0.0) (numbers.getD j 0.0) < threshold) ↔
    List.Pairwise (fun a b => absDiff a b ≥ threshold) numbers:= by 
  aesop?


end tmp