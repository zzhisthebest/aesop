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


theorem linearSearchAux_succ (a : Array Int) (e : Int) (n : Nat)
    (h₁ : n < a.size) (h₂ : a[n]! ≠ e) :
    linearSearchAux a e n = linearSearchAux a e (n + 1):= by
  aesop?
  simp_all only [getElem!_pos, ne_eq]
  induction n using tmp.linearSearchAux.induct a e
  · unfold tmp.linearSearchAux

    simp_all only [getElem!_pos, not_true_eq_false]
  · aesop_unfold tmp.linearSearchAux tmp.linearSearchAux
    simp_all only [getElem!_pos, not_false_eq_true, ↓reduceIte]
    split
    next x ih1 h =>
      simp_all only [getElem!_pos]
      simp_all only
      split
      next h_1 =>
        subst h_1
        simp_all only [not_true_eq_false, false_implies, imp_self]
        induction x with
        | zero =>
          unfold tmp.linearSearchAux
          simp_all only [Nat.zero_eq, Nat.zero_add, ↓reduceIte, getElem!_pos]
        | succ a_1 =>
          unfold tmp.linearSearchAux
          simp_all only [Nat.succ_eq_add_one, ↓reduceIte, getElem!_pos, Nat.add_left_cancel_iff]
      next h_1 => simp_all only [not_false_eq_true, forall_const]
    next x ih1 h =>
      simp_all only [forall_false, Nat.not_lt]
      induction x with
      | zero =>
        unfold tmp.linearSearchAux
        simp_all only [Nat.zero_eq, Nat.zero_add, getElem!_pos, Nat.reduceAdd, Nat.not_lt, getElem!_neg,
          Int.default_eq_zero, ite_eq_right_iff]
        intro a_1
        split
        next h_1 =>
          subst h_1
          simp_all only [Nat.succ_ne_self]
          grind
        next h_1 => grind
      | succ a_1 =>
        unfold tmp.linearSearchAux
        simp_all only [Nat.succ_eq_add_one, getElem!_pos, Nat.not_lt, getElem!_neg, Int.default_eq_zero,
          ite_eq_right_iff]
        intro a_2
        split
        next n_ih h_1 =>
          subst h_1
          simp_all only [Nat.add_eq_zero, Nat.succ_ne_self, and_false, and_self]
          grind
        next n_ih h_1 => grind
  · unfold tmp.linearSearchAux tmp.linearSearchAux
    simp_all only [not_true_eq_false]
  aesop?(config := { useDefaultSimpSet := false })


end tmp
