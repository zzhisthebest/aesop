import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x < a.size

def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1

def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  let best := a[0]!
  let m := findBest a x 1 best;
  let p := findP a x m x;
  (m, p)

@[reducible, simp]
def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)


theorem max_singleton (a : Array Int) (ha : a.size > 0) :
    findBest a 1 1 a[0]! = a[0]!:= by
  induction 1, a[0] using tmp.findBest.induct a 1
  rename_i h newBest ih1
  simp_all
  subst h
  simp_all only
  induction 0, a[0] using tmp.findBest.induct a 0
  · unfold tmp.findBest
    unfold tmp.findBest at ih1
    simp_all only [Nat.not_lt_zero]
  · unfold tmp.findBest
    unfold tmp.findBest at ih1
    simp_all only [Nat.not_lt_zero, not_false_eq_true, Nat.lt_irrefl, ↓reduceIte]
  rename_i i best h
  simp_all
  simp_all only
  induction i with
  | zero =>
    unfold tmp.findBest
    simp_all only [Nat.zero_eq, not_true_eq_false]
  | succ a_1 =>
    unfold tmp.findBest
    simp_all only [Nat.succ_eq_add_one, Nat.add_eq_zero, Nat.succ_ne_self, and_false, not_false_eq_true,
      Nat.lt_irrefl, ↓reduceIte]


end tmp
