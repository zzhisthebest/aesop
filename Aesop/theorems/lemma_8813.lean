module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_8813
public def uniqueProduct_precond (arr : Array Int) : Prop :=
  True

public def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  let rec loop (i : Nat) (seen : Std.HashSet Int) (product : Int) : Int :=
    if i < arr.size then
      let x := arr[i]!
      if seen.contains x then
        loop (i + 1) seen product
      else
        loop (i + 1) (seen.insert x) (product * x)
    else
      product
  loop 0 Std.HashSet.empty 1

public def uniqueProduct_postcond (arr : Array Int) (result: Int) (h_precond : uniqueProduct_precond (arr)) :=
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0


public theorem foldl_cons (x : Int) (xs : List Int) :
    List.foldl (· * ·) (1 : Int) (x :: xs) = (List.foldl (· * ·) (1 : Int) xs) * x:= by 
sorry


end tmp_lemma_8813