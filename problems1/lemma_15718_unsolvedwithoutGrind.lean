import Codetic
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

attribute [simp]
List.idxOf_append
#check List.idxOf_append
theorem idxOf_append_last (acc : List Int) (x : Int) (h : ¬ acc.contains x) :
    (acc ++ [x]).idxOf x = acc.length:= by
codetic?(config := { enableGrind := false })


end tmp
--终于找出一个simp定理！
