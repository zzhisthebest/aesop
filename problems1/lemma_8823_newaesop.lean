import Aesop
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


theorem prod_eq_of_nodup_mem_iff {l₁ l₂ : List Int}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.foldl (· * ·) 1 = l₂.foldl (· * ·) 1:= by 
  aesop?


end tmp