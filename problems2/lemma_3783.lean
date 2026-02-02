import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def mergeIntervals_precond (intervals : List (Prod Int Int)) : Prop :=
  True

def mergeIntervals (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : List (Prod Int Int) :=
  let rec insert (x : Prod Int Int) (sorted : List (Prod Int Int)) : List (Prod Int Int) :=
    match sorted with
    | [] => [x]
    | y :: ys => if x.fst ≤ y.fst then x :: sorted else y :: insert x ys

  let rec sort (xs : List (Prod Int Int)) : List (Prod Int Int) :=
    match xs with
    | [] => []
    | x :: xs' => insert x (sort xs')

  let sorted := sort intervals

  let rec merge (xs : List (Prod Int Int)) (acc : List (Prod Int Int)) : List (Prod Int Int) :=
    match xs, acc with
    | [], _ => acc.reverse
    | (s, e) :: rest, [] => merge rest [(s, e)]
    | (s, e) :: rest, (ps, pe) :: accTail =>
      if s ≤ pe then
        merge rest ((ps, max pe e) :: accTail)
      else
        merge rest ((s, e) :: (ps, pe) :: accTail)

  merge sorted []

@[reducible, simp]
def mergeIntervals_postcond (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : Prop :=
  let covered := intervals.all (fun (s, e) =>
    result.any (fun (rs, re) => rs ≤ s ∧ e ≤ re))

  let rec noOverlap (l : List (Prod Int Int)) : Bool :=
    match l with
    | [] | [_] => true
    | (_, e1) :: (s2, e2) :: rest => e1 < s2 && noOverlap ((s2, e2) :: rest)

  covered ∧ noOverlap result


theorem covered_by_merge
    (intervals : List (Prod Int Int))
    (h_precond : mergeIntervals_precond intervals) :
    intervals.all
      (fun (s, e) =>
        (mergeIntervals intervals h_precond).any
          (fun (rs, re) => rs ≤ s ∧ e ≤ re)):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp