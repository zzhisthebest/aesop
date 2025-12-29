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
aesop


end tmp