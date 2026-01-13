module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12528
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


public theorem foldl_eq_countLessThan_rec (numbers : Array Int) (threshold : Int) :
    numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 =
      (Nat.rec (motive := fun _ => Nat) 0
        (fun i ih =>
          if i < numbers.size then
            let new := if numbers[i]! < threshold then ih + 1 else ih
            new
          else ih)) numbers.size:= by 
sorry


end tmp_lemma_12528