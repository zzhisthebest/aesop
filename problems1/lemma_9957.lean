import Codetic
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


theorem toUppercase_char (s : String) (h : toUppercase_precond s)
    (i : Nat) (hi : i < s.length) :
    (isLowerCase (s.toList[i]!) → (toUppercase s h).toList[i]! = shiftMinus32 (s.toList[i]!)) ∧
    (¬ isLowerCase (s.toList[i]!) → (toUppercase s h).toList[i]! = s.toList[i]!):= by 
codetic?(config := { enableGrind := false })


end tmp