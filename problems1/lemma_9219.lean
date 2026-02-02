import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def differenceMinMax_precond (a : Array Int) : Prop :=
  a.size > 0

def differenceMinMax (a : Array Int) (h_precond : differenceMinMax_precond (a)) : Int :=
  let rec loop (i : Nat) (minVal maxVal : Int) : Int :=
    if i < a.size then
      let x := a[i]!
      let newMin := if x < minVal then x else minVal
      let newMax := if x > maxVal then x else maxVal
      loop (i + 1) newMin newMax
    else
      maxVal - minVal
  loop 1 (a[0]!) (a[0]!)

@[reducible, simp]
def differenceMinMax_postcond (a : Array Int) (result: Int) (h_precond : differenceMinMax_precond (a)) :=
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))


theorem add_left_neg (a : Int) : -a + a = (0 : Int):= by 
codetic?(config := { enableGrind := false })


end tmp