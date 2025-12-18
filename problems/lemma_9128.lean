import Aesop
set_option maxHeartbeats 0
namespace tmp
def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)

@[reducible, simp]
def dissimilarElements_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def dissimilarElements (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) : Array Int :=
  let res := a.foldl (fun acc x => if !inArray b x then acc.insert x else acc) Std.HashSet.empty
  let res := b.foldl (fun acc x => if !inArray a x then acc.insert x else acc) res
  res.toArray.insertionSort

@[reducible, simp]
def dissimilarElements_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : dissimilarElements_precond (a) (b)) :=
  result.all (fun x => inArray a x ≠ inArray b x)∧
  result.toList.Pairwise (· ≤ ·) ∧
  a.all (fun x => if x ∈ b then x ∉ result else x ∈ result) ∧
  b.all (fun x => if x ∈ a then x ∉ result else x ∈ result)


theorem filter_b_pred (a b : Array Int) :
    (b.filter fun x => !(inArray a x)).all (fun x => inArray a x ≠ inArray b x) = true:= by 
  aesop?
  aesop?(config := { useDefaultSimpSet := false })


end tmp