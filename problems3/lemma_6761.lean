import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def task_code_precond (sequence : List Int) : Prop :=
  True

def task_code (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  match sequence with
  | []      => 0
  | x :: xs =>
      let (_, maxSoFar) :=
        xs.foldl (fun (acc : Int × Int) (x : Int) =>
          let (cur, maxSoFar) := acc
          let newCur := if cur + x >= x then cur + x else x
          let newMax := if maxSoFar >= newCur then maxSoFar else newCur
          (newCur, newMax)
        ) (x, x)
      maxSoFar

@[reducible, simp]
def task_code_postcond (sequence : List Int) (result: Int) (h_precond : task_code_precond (sequence)) : Prop :=
  let subArrays :=
    List.range (sequence.length + 1) |>.flatMap (fun start =>
      List.range (sequence.length - start + 1) |>.map (fun len =>
        sequence.drop start |>.take len))
  let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum)
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)


theorem foldl_add (xs : List Int) (z : Int) :
    xs.foldl (fun a b => a + b) z = z + xs.sum:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp