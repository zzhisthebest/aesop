module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_9201
public def differenceMinMax_precond (a : Array Int) : Prop :=
  a.size > 0

public def differenceMinMax (a : Array Int) (h_precond : differenceMinMax_precond (a)) : Int :=
  let rec loop (i : Nat) (minVal maxVal : Int) : Int :=
    if i < a.size then
      let x := a[i]!
      let newMin := if x < minVal then x else minVal
      let newMax := if x > maxVal then x else maxVal
      loop (i + 1) newMin newMax
    else
      maxVal - minVal
  loop 1 (a[0]!) (a[0]!)

public def differenceMinMax_postcond (a : Array Int) (result: Int) (h_precond : differenceMinMax_precond (a)) :=
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))


public theorem foldl_max_ge (a : Array Int) (i : Nat) (h : i < a.size) :
    (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!)) ≥ a[i]!:= by 
sorry


end tmp_lemma_9201