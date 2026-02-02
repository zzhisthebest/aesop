import Codetic
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


theorem sub_zero_and_ge_of_eq (x y : Int) (h : x = y) :
    x - y = 0 ∧ x ≥ y:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp