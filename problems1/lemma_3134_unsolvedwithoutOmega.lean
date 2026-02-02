import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def maxProfit_precond (prices : List Nat) : Prop :=
  True

def updateMinAndProfit (price : Nat) (minSoFar : Nat) (maxProfit : Nat) : (Nat × Nat) :=
  let newMin := Nat.min minSoFar price
  let profit := if price > minSoFar then price - minSoFar else 0
  let newMaxProfit := Nat.max maxProfit profit
  (newMin, newMaxProfit)

def maxProfitAux (prices : List Nat) (minSoFar : Nat) (maxProfit : Nat) : Nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let (newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit
    maxProfitAux ps newMin newProfit

def maxProfit (prices : List Nat) (h_precond : maxProfit_precond (prices)) : Nat :=
  match prices with
  | [] => 0
  | p :: ps => maxProfitAux ps p 0

@[reducible, simp]
def maxProfit_postcond (prices : List Nat) (result: Nat) (h_precond : maxProfit_precond (prices)) : Prop :=
  (result = 0 ∧ prices = []) ∨
  (
    List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ result) prices.zipIdx ∧

    prices.zipIdx.any (fun ⟨pi, i⟩ =>
      prices.zipIdx.any (fun ⟨pj, j⟩ =>
        i < j ∧ pj - pi = result))
  )


theorem maxProfit_result_cons (p : Nat) (ps : List Nat)
    (h : maxProfit_precond (p :: ps)) :
    maxProfit (p :: ps) h = maxProfitAux ps p 0:= by 
codetic?(config := { enableGrind := false })


end tmp