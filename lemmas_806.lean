import Aesop
set_option maxHeartbeats 0
set_option trace.aesop.zzh_custom true
namespace tmp
@[reducible]
def firstDuplicate_precond (lst : List Int) : Prop :=
  True

def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Int :=
  let rec helper (seen : List Int) (rem : List Int) : Int :=
    match rem with
    | [] => -1
    | h :: t => if seen.contains h then h else helper (h :: seen) t
  helper [] lst

@[reducible]
def firstDuplicate_postcond (lst : List Int) (result: Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  (result = -1 → List.Nodup lst) ∧
  (result ≠ -1 →
    lst.count result > 1 ∧
    (lst.filter (fun x => lst.count x > 1)).head? = some result
  )

#check List.forIn'_loop_congr
theorem count_cons_of_ne {x y : Int} (h : x ≠ y) (xs : List Int) :
    (y :: xs).count x = xs.count x:= by
  --simp [List.count_cons]
  aesop

#check @Nat.lt_trans

theorem myLeTrans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  aesop (add unsafe 90% apply Nat.le_trans)

end tmp
