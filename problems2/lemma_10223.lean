import Aesop
set_option maxHeartbeats 0
namespace tmp
def isEven (n : Int) : Bool :=
  n % 2 = 0

@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True

def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]

@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)


theorem order_preserved (arr : Array Int) (x y : Int)
    (hx₁ : x ∈ arr.toList) (hy₁ : y ∈ arr.toList)
    (hxE : isEven x) (hyE : isEven y)
    (hidx : arr.toList.idxOf x ≤ arr.toList.idxOf y) :
    (findEvenNumbers arr (by trivial)).toList.idxOf x ≤
      (findEvenNumbers arr (by trivial)).toList.idxOf y:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp