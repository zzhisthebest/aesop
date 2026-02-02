import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = e

def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  linearSearchAux a e 0

@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)


theorem linearSearchAux_first (a : Array Int) (e : Int) (n i : Nat)
    (h₁ : n ≤ i) (h₂ : i < a.size) (h₃ : a[i]! = e)
    (h₄ : ∀ k, n ≤ k → k < i → a[k]! ≠ e) :
    linearSearchAux a e n = i:= by
subst h₃
simp_all only [getElem!_pos, ne_eq]
induction n using tmp.linearSearchAux.induct a a[i]
· unfold tmp.linearSearchAux
  simp_all only [getElem!_pos, ↓reduceIte]
  rename_i x h1 h2
  by_cases x=i
  codetic
  have h3:x<i:=by codetic
  have h4:¬a[x]! = a[i]:=by codetic
  codetic
  -- induction i with
  -- | zero =>
  --   simp_all only [Nat.zero_eq, Nat.le_zero_eq, Nat.zero_le, Nat.not_lt_zero, false_implies, imp_self, implies_true]
  -- | succ a_1 =>
  --   simp_all only [Nat.succ_eq_add_one]
  --   --grind
  --   rename_i x h1 h2 h3

  --   --clear h2
  --   grind
    --codetic?(config := { enableGrind := false })
· unfold tmp.linearSearchAux
  simp_all only [getElem!_pos, ↓reduceIte]

  --codetic?(config := { enableGrind := false })
· unfold tmp.linearSearchAux
  simp_all only [Nat.not_lt, getElem!_pos, getElem!_neg, Int.default_eq_zero]
  split
  next x h h_1 =>
    split
    next h_2 => omega
    next h_2 => omega
  next x h h_1 =>
    simp_all only [Nat.not_lt]
    omega
codetic?(config := { enableGrind := false })


end tmp
--提取不出来定理
