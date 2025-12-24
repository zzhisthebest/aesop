import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def moveZeroes_precond (xs : List Int) : Prop :=
  True

def moveZeroes (xs : List Int) (h_precond : moveZeroes_precond (xs)) : List Int :=
  let nonzeros := xs.filter (fun x => x ≠ 0)
  let zeros := xs.filter (fun x => x = 0)
  nonzeros ++ zeros

def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt

@[reducible]
def moveZeroes_postcond (xs : List Int) (result: List Int) (h_precond : moveZeroes_precond (xs)) : Prop :=
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧

  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧

  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length


theorem dropWhile_all_zero (xs : List Int) :
    ((moveZeroes xs (by trivial)).dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) = true:= by 
  aesop?


end tmp