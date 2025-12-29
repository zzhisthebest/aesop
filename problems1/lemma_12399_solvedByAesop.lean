import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
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

def CanyonSearch (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) : Nat :=
  let init : Nat :=
    if a[0]! < b[0]! then (b[0]! - a[0]!).natAbs
    else (a[0]! - b[0]!).natAbs
  canyonSearchAux a b 0 0 init

@[reducible, simp]
def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))


theorem canyonStep (a b : Array Int) (m n d : Nat) (hm : m < a.size) (hn : n < b.size) :
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    (if a[m]! ≤ b[n]! then canyonSearchAux a b (m+1) n new_d
                     else canyonSearchAux a b m (n+1) new_d) =
    canyonSearchAux a b (if a[m]! ≤ b[n]! then m+1 else m)
                     (if a[m]! ≤ b[n]! then n else n+1) new_d:= by 
aesop


end tmp