import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isPeakValley_precond (lst : List Int) : Prop :=
  True

def isPeakValley (lst : List Int) (h_precond : isPeakValley_precond (lst)) : Bool :=
  let rec aux (l : List Int) (increasing : Bool) (startedDecreasing : Bool) : Bool :=
    match l with
    | x :: y :: rest =>
      if x < y then
        if startedDecreasing then false
        else aux (y :: rest) true startedDecreasing
      else if x > y then
        if increasing then aux (y :: rest) increasing true
        else false
      else false
    | _ => increasing && startedDecreasing
  aux lst false false

@[reducible, simp]
def isPeakValley_postcond (lst : List Int) (result: Bool) (h_precond : isPeakValley_precond (lst)) : Prop :=
  let len := lst.length
  let validPeaks :=
    List.range len |>.filter (fun p =>
      1 ≤ p ∧ p < len - 1 ∧

      (List.range p).all (fun i =>
        lst[i]! < lst[i + 1]!
      ) ∧

      (List.range (len - 1 - p)).all (fun i =>
        lst[p + i]! > lst[p + i + 1]!
      )
    )
  (validPeaks != [] → result) ∧
  (validPeaks.length = 0 → ¬ result)


theorem List.get?_some {α} (l : List α) (i : Nat) (h : i < l.length) :
  l.get? i = some (l.get ⟨i, h⟩):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp