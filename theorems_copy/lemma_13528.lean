module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_13528
public def IsPalindrome_precond (x : List Char) : Prop :=
  True

public def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false
  else true

public def IsPalindrome (x : List Char) (h_precond : IsPalindrome_precond (x)) : Bool :=
  if x.length = 0 then true else isPalindromeHelper x 0 (x.length - 1)

public def IsPalindrome_postcond (x : List Char) (result: Bool) (h_precond : IsPalindrome_precond (x)) :=
  result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)


public theorem isPalindromeHelper_bounds (x : List Char) {i j : Nat}
    (hij : i ≤ j) (hjl : j < x.length) :
    (x[i]? = none) → False:= by 
sorry


end tmp_lemma_13528