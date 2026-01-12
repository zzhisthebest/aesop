module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_15732
public def SetToSeq_precond (s : List Int) : Prop :=
  True

public def SetToSeq (s : List Int) (h_precond : SetToSeq_precond (s)) : List Int :=
  s.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

public def SetToSeq_postcond (s : List Int) (result: List Int) (h_precond : SetToSeq_precond (s)) :=
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  result.all (fun a => result.count a = 1) ∧
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result


public theorem foldl_nodup_count (s : List Int) :
    (s.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []).all
        (fun a => (s.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []).count a = 1):= by 
sorry


end tmp_lemma_15732