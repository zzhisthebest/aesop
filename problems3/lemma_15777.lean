import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def SetToSeq_precond (s : List Int) : Prop :=
  True

def SetToSeq (s : List Int) (h_precond : SetToSeq_precond (s)) : List Int :=
  s.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

@[reducible, simp]
def SetToSeq_postcond (s : List Int) (result: List Int) (h_precond : SetToSeq_precond (s)) :=
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  result.all (fun a => result.count a = 1) ∧
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result


theorem order_preserved (s : List Int) (a b : Int) :
    a ∈ SetToSeq s (by trivial) →
    b ∈ SetToSeq s (by trivial) →
    (SetToSeq s (by trivial)).idxOf a < (SetToSeq s (by trivial)).idxOf b →
    s.idxOf a < s.idxOf b:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp