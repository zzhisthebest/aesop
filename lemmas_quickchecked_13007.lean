import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Find_precond (a : Array Int) (key : Int) : Prop :=
  True

def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0

@[reducible, simp]
def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)


theorem Find.search_nonneg_or_neg_one (a : Array Int) (key : Int) :
    ∀ i : Nat, (Find.search a key i = -1) ∨ (0 ≤ Find.search a key i):= by
  intro i
  induction i using tmp.Find.search.induct a key
  · unfold tmp.Find.search
    subst h✝
    simp_all only [↓reduceIte, getElem!_pos, Int.ofNat_eq_coe, Int.reduceNeg, reduceCtorEq, Int.ofNat_zero_le,
      or_true]
  · unfold tmp.Find.search
    simp_all only [getElem!_pos, Int.reduceNeg, ↓reduceIte]
  · unfold tmp.Find.search
    simp_all only [Nat.not_lt, getElem!_pos, Int.ofNat_eq_coe, getElem!_neg, Int.default_eq_zero, Int.reduceNeg,
      ite_eq_right_iff]
    split
    next x h h_1 =>
      subst h_1
      simp_all only [Int.reduceNeg, reduceCtorEq, imp_false, Nat.not_lt, true_or]
    next x h h_1 =>
      split
      next h_2 =>
        simp_all only [Int.reduceNeg, forall_const]
        grind
      next h_2 =>
        simp_all only [Nat.not_lt, Int.reduceNeg, Int.neg_nonneg, Int.reduceLE, or_false]
        intro a_1
        grind
  aesop?(config := { useDefaultSimpSet := false })


end tmp
