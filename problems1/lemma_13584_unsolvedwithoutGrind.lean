import Aesop
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
@[simp]
theorem eq_of_le_and_forall_ne {α : Type} [Inhabited α] (l : List α) (v : α) (n x : Nat)
  (h_bound : n < l.length)
  (h_val : l[n] = v)              -- n处的值是v (对应你的 h3)
  (h_le : x ≤ n)                  -- x在范围内 (对应你的 hle)
  (h_pre : ∀ k < n, l[k]! ≠ v)     -- n之前没有v (对应你的 hno)
  (h_x_val : l[x] = v)            -- x处的值也是v
  : x = n := by
  -- 证明逻辑
  by_contra h_ne
  have h_lt : x < n := Nat.lt_of_le_of_ne h_le h_ne
  have h_contra := h_pre x h_lt
  grind

theorem aux_eq_min (a : Array Int) (e : Int) (n i : Nat)
    (hle : n ≤ i)
    (hi_lt : i < a.size) (hi_eq : a[i]! = e)
    (hno  : ∀ k, k < i → a[k]! ≠ e) :
    linearSearchAux a e n = i:= by
subst hi_eq
simp_all only [getElem!_pos, ne_eq]
induction n using tmp.linearSearchAux.induct a a[i]
· unfold tmp.linearSearchAux
  simp_all only [getElem!_pos, ↓reduceIte]
  induction i with
  | zero => simp_all only [Nat.zero_eq, Nat.not_lt_zero, false_implies, implies_true, Nat.le_zero_eq]
  | succ a_1 =>
    simp_all only [Nat.succ_eq_add_one]
    --grind
    rename_i x h1 h2 h3
    apply eq_of_le_and_forall_ne
    aesop?(config := { enableGrind := false })


· unfold tmp.linearSearchAux
  simp_all only [getElem!_pos, ↓reduceIte]
  grind
· unfold tmp.linearSearchAux
  simp_all only [Nat.not_lt, getElem!_pos, getElem!_neg, Int.default_eq_zero]
  split
  next x h h_1 =>
    split
    next h_2 => grind
    next h_2 => grind
  next x h h_1 =>
    simp_all only [Nat.not_lt]

    --grind

aesop?(config := { enableGrind := false })


end tmp
