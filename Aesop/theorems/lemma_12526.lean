module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12526
public def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  True

public def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0

public def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  countLessThan numbers threshold

public def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0


public theorem foldl_eq_rec (as : Array Int) (f : Nat → Int → Nat) (init : Nat) :
    as.foldl f init =
      (Nat.rec (motive := fun _ => Nat) init
        (fun i ih =>
          if i < as.size then
            let new := f ih (as[i]!)
            new
          else ih)) as.size:= by 
sorry


end tmp_lemma_12526