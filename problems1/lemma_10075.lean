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


theorem array_foldl_push_eq_filter (as : Array Int) :
    (as.foldl (fun (acc : Array Int) (x : Int) =>
        if isEven x then acc.push x else acc) #[]).toList =
      as.toList.filter (fun x => isEven x):= by 
aesop


end tmp