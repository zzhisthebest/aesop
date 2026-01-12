module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_4889
public def moveZeroes_precond (xs : List Int) : Prop :=
  True

public def moveZeroes (xs : List Int) (h_precond : moveZeroes_precond (xs)) : List Int :=
  let nonzeros := xs.filter (fun x => x ≠ 0)
  let zeros := xs.filter (fun x => x = 0)
  nonzeros ++ zeros

public def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

public def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt

public def moveZeroes_postcond (xs : List Int) (result: List Int) (h_precond : moveZeroes_precond (xs)) : Prop :=
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧

  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧

  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length


public theorem dropWhile_concat_nonzeros (xs zs : List Int)
    (hxs : ∀ x ∈ xs, (x ≠ 0) = true) :
    (xs ++ zs).dropWhile (fun x => x ≠ 0) = zs:= by 
sorry


end tmp_lemma_4889