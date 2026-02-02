import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  True

def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0

def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  countLessThan numbers threshold

@[reducible, simp]
def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0


theorem count_step_eq_foldl_step
    (numbers : Array Int) (threshold : Int) (i : Nat) (acc : Nat)
    (h : i < numbers.size) :
    (if numbers[i]! < threshold then acc + 1 else acc) =
      (fun c n => if n < threshold then c + 1 else c) acc (numbers[i]! ):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp