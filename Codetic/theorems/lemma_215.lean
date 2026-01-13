module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_215
public def findMajorityElement_precond (lst : List Int) : Prop :=
  True

public def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0

public def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  let n := lst.length
  let majority := lst.find? (fun x => countOccurrences x lst > n / 2)
  match majority with
  | some x => x
  | none => -1

public def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)


public theorem foldl_add_const (c : Nat) (n : Int) (lst : List Int) :
    lst.foldl (fun acc x => if x = n then acc + 1 else acc) c =
      c + lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0:= by 
sorry


end tmp_lemma_215