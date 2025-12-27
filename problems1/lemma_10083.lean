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


theorem findEvenNumbers_order (arr : Array Int) (h_precond)
    {x y : Int} (hx_arr : x ∈ arr.toList) (hy_arr : y ∈ arr.toList)
    (hx_even : isEven x) (hy_even : isEven y)
    (hidx : arr.toList.idxOf x ≤ arr.toList.idxOf y) :
    (findEvenNumbers arr h_precond).toList.idxOf x ≤
      (findEvenNumbers arr h_precond).toList.idxOf y:= by 
aesop


end tmp