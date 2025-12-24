import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def arraySum_precond (a : Array Int) : Prop :=
  a.size > 0

def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  a.toList.sum

def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!

@[reducible, simp]
def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size


theorem sumTo_eq_sum_take (a : Array Int) {n : Nat} (hn : n ≤ a.size) :
    sumTo a n = (a.toList.take n).sum:= by 
  aesop?


end tmp