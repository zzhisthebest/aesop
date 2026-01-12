import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  True

def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  let rec helper (n : Nat) : Bool :=
    match n with
    | 0 =>
      false
    | Nat.succ m =>
      match m with
      | 0 =>
        true
      | Nat.succ l =>
        if (l+2)%4=0 then
          helper ((l+2)/4)
        else
          false
  helper n

@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)


theorem ifPowerOfFour_of_pow (m : Nat) :
    ifPowerOfFour (4 ^ m) (by trivial) = true:= by
simp_all only [ifPowerOfFour]
induction m with
| zero =>
  unfold tmp.ifPowerOfFour.helper
  simp_all only
| succ a =>
  unfold tmp.ifPowerOfFour.helper
  simp_all only [Nat.succ_eq_add_one, Bool.if_false_right]
  split
  next n_ih m heq =>
    simp_all only [Nat.pow_eq_zero, reduceCtorEq, ne_eq, Nat.add_eq_zero, Nat.succ_ne_self, and_false,
      not_false_eq_true, and_true]
  next n_ih m l heq =>
    simp_all only [Nat.succ_eq_add_one]
    split
    next m_1 =>
      simp_all only [Nat.zero_add, Nat.pow_eq_one, Nat.reduceEqDiff, Nat.add_eq_zero, Nat.succ_ne_self, and_false,
        or_self]
    next m_1 l =>
      simp_all only [Nat.succ_eq_add_one, Bool.and_eq_true, decide_eq_true_eq]
      apply And.intro
      · grind
      · grind
aesop?(config := { enableGrind := false })


end tmp
--提不出来simp定理
