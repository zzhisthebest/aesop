import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True

def replaceChars (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if c = oldChar then newChar else c)
  String.mk cs'

@[reducible, simp]
def replaceChars_postcond (s : String) (oldChar : Char) (newChar : Char) (result: String) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :=
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < cs.length →
    (cs[i]! = oldChar → cs'[i]! = newChar) ∧
    (cs[i]! ≠ oldChar → cs'[i]! = cs[i]!))


theorem replaceChars_get (s : String) (old new : Char)
    (h : replaceChars_precond s old new) (i : Nat) (hi : i < s.toList.length) :
    (replaceChars s old new h).toList.get! i =
      if s.toList.get! i = old then new else s.toList.get! i:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp