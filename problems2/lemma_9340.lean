import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def sumAndAverage_precond (n : Nat) : Prop :=
  True

def sumAndAverage (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
  if n ≤ 0 then (0, 0.0)
  else
    let sum := (List.range (n + 1)).sum
    let average : Float := sum.toFloat / (n.toFloat)
    (sum, average)

@[reducible, simp]
def sumAndAverage_postcond (n : Nat) (result: Int × Float) (h_precond : sumAndAverage_precond (n)) :=
  (n = 0 → result == (0, 0.0)) ∧
  (n > 0 →
    result.1 == n * (n + 1) / 2 ∧
    result.2 == ((n * (n + 1) / 2).toFloat) / (n.toFloat))


theorem sum_range_eq (n : Nat) : (List.range (n + 1)).sum = n * (n + 1) / 2:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp