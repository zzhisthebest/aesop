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


theorem foldl_even_prop (arr : Array Int) :
    let res := arr.foldl
                (fun (acc : Array Int) (x : Int) =>
                  if isEven x then acc.push x else acc) #[]
    (∀ x, x ∈ res → isEven x ∧ x ∈ arr.toList) ∧
    (∀ x, x ∈ arr.toList → isEven x → x ∈ res) ∧
    (∀ x y,
        x ∈ arr.toList → y ∈ arr.toList →
        isEven x → isEven y →
        arr.toList.idxOf x ≤ arr.toList.idxOf y →
        res.toList.idxOf x ≤ res.toList.idxOf y):= by 
  aesop?


end tmp