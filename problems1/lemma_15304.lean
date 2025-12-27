import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def replace_precond (arr : Array Int) (k : Int) : Prop :=
  True

def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc

def replace (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  replace_loop arr k 0 arr

@[reducible, simp]
def replace_postcond (arr : Array Int) (k : Int) (result: Array Int) (h_precond : replace_precond (arr) (k)) :=
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
  (∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))


theorem replace_loop_get_aux
    (arr : Array Int) (k : Int) (i : Nat) (hi : i < arr.size) :
    (replace_loop arr k 0 arr)[i]! = if arr[i]! > k then -1 else arr[i]!:= by 
aesop


end tmp