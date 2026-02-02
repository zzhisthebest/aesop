import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def IsPalindrome_precond (x : List Char) : Prop :=
  True

def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false
  else true

def IsPalindrome (x : List Char) (h_precond : IsPalindrome_precond (x)) : Bool :=
  if x.length = 0 then true else isPalindromeHelper x 0 (x.length - 1)

@[reducible, simp]
def IsPalindrome_postcond (x : List Char) (result: Bool) (h_precond : IsPalindrome_precond (x)) :=
  result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)


theorem sub_eq_add_sub (i j : Nat) (h : i ≤ j) : j - i = i + j - (2 * i):= by 
codetic?(config := { enableGrind := false })


end tmp