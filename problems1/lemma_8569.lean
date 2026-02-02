import Codetic
set_option maxHeartbeats 0
namespace tmp
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)

@[reducible, simp]
def toLowercase_precond (s : String) : Prop :=
  True

def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isUpperCase c then shift32 c else c)
  String.mk cs'

@[reducible, simp]
def toLowercase_postcond (s : String) (result: String) (h_precond : toLowercase_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))


theorem mk_toList (l : List Char) : (String.mk l).toList = l:= by 
codetic?(config := { enableGrind := false })


end tmp