import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def maxCoverageAfterRemovingOne_precond (intervals : List (Prod Nat Nat)) : Prop :=
  intervals.length > 0

def maxCoverageAfterRemovingOne (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Nat :=
  let n := intervals.length
  if n ≤ 1 then 0
  else
    (List.range n).foldl (fun acc i =>
      let remaining := List.eraseIdx intervals i
      let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged := sorted.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let coverage := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      max acc coverage
    ) 0

@[reducible, simp]
def maxCoverageAfterRemovingOne_postcond (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Prop :=
  ∃ i < intervals.length,
    let remaining := List.eraseIdx intervals i
    let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
    let merged := sorted.foldl (fun acc curr =>
      match acc with
      | [] => [curr]
      | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
    ) []
    let cov := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
    result = cov ∧
    ∀ j < intervals.length,
      let rem_j := List.eraseIdx intervals j
      let sort_j := List.mergeSort rem_j (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged_j := sort_j.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let cov_j := merged_j.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      cov ≥ cov_j


theorem foldl_max_eq_foldl (xs : List Nat) (a : Nat) :
    xs.foldl max a = (a :: xs).foldl max 0:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp