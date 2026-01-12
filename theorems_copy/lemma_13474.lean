module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_13474
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


public theorem get?_some_iff_lt (x : List Char) (i : Nat) (c : Char) :
    x[i]? = some c ↔ i < x.length ∧ x[i]! = c:= by 
sorry


end tmp_lemma_13474