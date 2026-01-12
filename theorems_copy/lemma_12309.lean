module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_12309
public def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

public def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n

public def CanyonSearch (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) : Nat :=
  let init : Nat :=
    if a[0]! < b[0]! then (b[0]! - a[0]!).natAbs
    else (a[0]! - b[0]!).natAbs
  canyonSearchAux a b 0 0 init

public def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))


public theorem new_d_le_old (diff d : Nat) :
    (if diff < d then diff else d) ≤ d:= by 
sorry


end tmp_lemma_12309