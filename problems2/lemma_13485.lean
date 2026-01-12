import Aesop
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


theorem succ_sub_succ (a b : Nat) : Nat.succ a - Nat.succ b = a - b:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp