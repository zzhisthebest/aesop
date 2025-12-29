import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def maxSubarraySum_precond (xs : List Int) : Prop :=
  True

def maxSubarraySum (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) : Int :=
  let rec helper (lst : List Int) (curMax : Int) (globalMax : Int) : Int :=
    match lst with
    | [] => globalMax
    | x :: rest =>
      let newCurMax := max x (curMax + x)
      let newGlobal := max globalMax newCurMax
      helper rest newCurMax newGlobal
  match xs with
  | [] => 0
  | x :: rest => helper rest x x

@[reducible, simp]
def maxSubarraySum_postcond (xs : List Int) (result: Int) (h_precond : maxSubarraySum_precond (xs)) : Prop :=
  let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start =>
    List.range' 1 (xs.length - start) |>.map (fun len =>
      ((xs.drop start).take len).sum
    ))

  let has_result_subarray := subarray_sums.any (fun sum => sum == result)


  let is_maximum := subarray_sums.all (· ≤ result)

  match xs with
  | [] => result == 0
  | _ => has_result_subarray ∧ is_maximum


theorem sum_cons (x : Int) (xs : List Int) :
    (x :: xs).sum = x + xs.sum:= by 
aesop


end tmp