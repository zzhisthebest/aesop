import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def uniqueProduct_precond (arr : Array Int) : Prop :=
  True

def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
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

@[reducible, simp]
def uniqueProduct_postcond (arr : Array Int) (result: Int) (h_precond : uniqueProduct_precond (arr)) :=
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0


theorem uniqueProduct_eq_foldl (arr : Array Int)
    (h_pre : uniqueProduct_precond arr) :
    uniqueProduct arr h_pre =
      (arr.toList.eraseDups.foldl (· * ·) 1):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp