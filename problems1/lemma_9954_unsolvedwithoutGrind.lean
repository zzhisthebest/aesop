import Aesop
set_option maxHeartbeats 0
namespace tmp
def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)

@[reducible, simp]
def toUppercase_precond (s : String) : Prop :=
  True

def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isLowerCase c then shiftMinus32 c else c)
  String.mk cs'

@[reducible, simp]
def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))


theorem if_lowercase_cases (c : Char) :
    (isLowerCase c → (if isLowerCase c then shiftMinus32 c else c) = shiftMinus32 c) ∧
    (¬ isLowerCase c → (if isLowerCase c then shiftMinus32 c else c) = c):= by
simp_all only [isLowerCase, ↓Char.isValue, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, and_self,
  decide_true, ↓reduceIte, shiftMinus32, implies_true, not_and, Char.not_le, ite_eq_right_iff, and_imp, true_and]
intro a a_1 a_2
simp_all only [↓Char.isValue, forall_const]
--a和a_2矛盾。
sorry


end tmp
