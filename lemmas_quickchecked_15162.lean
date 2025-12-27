import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def remove_front_precond (a : Array Int) : Prop :=
  a.size > 0

def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc

def remove_front (a : Array Int) (h_precond : remove_front_precond (a)) : Array Int :=
  if a.size > 0 then
    let c := copyFrom a 1 (Array.mkEmpty (a.size - 1))
    c
  else
    panic "Precondition violation: array is empty"

@[reducible, simp]
def remove_front_postcond (a : Array Int) (result: Array Int) (h_precond : remove_front_precond (a)) :=
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)


theorem copyFrom_step_true (a : Array Int) (i : Nat) (acc : Array Int)
    (h : i < a.size) :
    copyFrom a i acc =
      copyFrom a (i + 1) (acc.push (a[i]!)):= by
  simp_all only [getElem!_pos]
  induction i, acc using tmp.copyFrom.induct a
  · unfold tmp.copyFrom
    rename_i i acc h_1 ih1
    simp_all only [getElem!_pos, ↓reduceIte]
    split
    next h_1 => simp_all only [getElem!_pos]
    next h_1 =>
      simp_all only [forall_false, Nat.not_lt]
      induction i with
      | zero =>
        unfold tmp.copyFrom
        simp_all only [Nat.zero_eq, Nat.zero_add, Nat.reduceAdd, getElem!_pos, Nat.not_lt, getElem!_neg,
          Int.default_eq_zero, ite_eq_right_iff]
        intro a_1
        grind
      | succ a_1 =>
        unfold tmp.copyFrom
        simp_all only [Nat.succ_eq_add_one, getElem!_pos, Nat.not_lt, getElem!_neg, Int.default_eq_zero,
          ite_eq_right_iff]
        intro a_2
        grind
  · unfold tmp.copyFrom
    simp_all only [not_true_eq_false]


end tmp
