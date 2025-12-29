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


theorem replaceChars_char (s : String) (old new : Char)
    (h_precond : replaceChars_precond s old new) :
    ∀ i,
      i < s.toList.length →
        (s.toList[i]! = old → (replaceChars s old new h_precond).toList[i]! = new) ∧
        (s.toList[i]! ≠ old → (replaceChars s old new h_precond).toList[i]! = s.toList[i]!):= by 
aesop


end tmp