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


theorem countVal_append_of_not (v : Int) (xs ys : List Int)
    (h : xs.all (fun x => x ≠ v) = true) :
    countVal v (xs ++ ys) = countVal v ys:= by
  simp_all only [ne_eq, decide_not, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  induction xs with
  | nil =>
    unfold tmp.countVal tmp.countVal
    simp_all only [List.not_mem_nil, false_implies, implies_true, List.nil_append]
  | cons head tail =>
    unfold tmp.countVal tmp.countVal
    simp_all only [List.mem_cons, or_true, not_false_eq_true, implies_true, forall_const, forall_eq_or_imp,
      List.cons_append, ↓reduceIte]
    obtain ⟨left, right⟩ := h

    split
    next x tail_ih =>
      simp_all only [List.append_nil]
      aesop?(config := { useDefaultSimpSet := false })
    aesop?(config := { useDefaultSimpSet := false })


end tmp
