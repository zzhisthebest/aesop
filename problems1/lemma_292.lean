import Aesop
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


theorem result_eq_some_of_ne_neg_one {lst : List Int} {h_precond}
    (h : findMajorityElement lst h_precond ≠ -1) :
    ∃ x, lst.find? (fun y => countOccurrences y lst > lst.length / 2) = some x ∧
         findMajorityElement lst h_precond = x:= by 
aesop?(config := { enableGrind := false })


end tmp