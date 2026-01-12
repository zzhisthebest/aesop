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


theorem foldl_idx_preserve (l : List Int) :
    ∀ a b,
      a ∈ l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) [] →
      b ∈ l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) [] →
      (l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []).idxOf a <
      (l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []).idxOf b →
      l.idxOf a < l.idxOf b:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp