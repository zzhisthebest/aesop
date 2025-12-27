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


theorem take_sum_succ (a : Array Int) (n : Nat) (h : n < a.size) :
    (a.toList.take (n.succ)).sum = (a.toList.take n).sum + a[n]!:= by 
aesop


end tmp