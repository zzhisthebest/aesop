module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_11474
public def arraySum_precond (a : Array Int) : Prop :=
  a.size > 0

public def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  a.toList.sum

public def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!

public def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size


public theorem take_sum_succ (a : Array Int) (n : Nat) :
    (a.toList.take (n + 1)).sum = (a.toList.take n).sum + a[n]!:= by 
sorry


end tmp_lemma_11474