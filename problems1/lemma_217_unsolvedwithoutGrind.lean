import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def findMajorityElement_precond (lst : List Int) : Prop :=
  True

def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0

def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  let n := lst.length
  let majority := lst.find? (fun x => countOccurrences x lst > n / 2)
  match majority with
  | some x => x
  | none => -1

@[reducible, simp]
def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

theorem find?_some_iff {α : Type} (p : α → Bool) (lst : List α) (x : α) :
  List.find? p lst = some x ↔
  ∃ (pre : List α) (post : List α),
    lst = pre ++ x :: post ∧
    p x = true ∧
    (∀ y ∈ pre, p y = false):=by
  codetic

#check List.find?_some
theorem majority_pred_holds (lst : List Int) (n : Nat) (x : Int)
    (h : lst.find? (fun y => countOccurrences y lst > n / 2) = some x) :
    countOccurrences x lst > n / 2:= by
simp_all only [countOccurrences, gt_iff_lt]
apply List.find?_some
grind
codetic?(config := { enableGrind := false })


end tmp
--似乎提不出来定理
