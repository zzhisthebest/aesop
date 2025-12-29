import Aesop
set_option maxHeartbeats 0
namespace tmp
def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false

@[reducible, simp]
def replaceWithColon_precond (s : String) : Prop :=
  True

def replaceWithColon (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isSpaceCommaDot c then ':' else c)
  String.mk cs'

@[reducible, simp]
def replaceWithColon_postcond (s : String) (result: String) (h_precond : replaceWithColon_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < s.length →
    (isSpaceCommaDot cs[i]! → cs'[i]! = ':') ∧
    (¬isSpaceCommaDot cs[i]! → cs'[i]! = cs[i]!))


theorem nth_replaceWithColon (s : String) (h : replaceWithColon_precond s)
    {i : Nat} (hi : i < s.length) :
    let c  := s.toList[i]!
    let c' := (replaceWithColon s h).toList[i]!
    (isSpaceCommaDot c → c' = ':') ∧
    (¬ isSpaceCommaDot c → c' = c):= by 
aesop


end tmp