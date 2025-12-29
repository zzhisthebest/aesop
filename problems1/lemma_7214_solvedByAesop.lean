import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def canCompleteCircuit_precond (gas : List Int) (cost : List Int) : Prop :=
  True

def canCompleteCircuit (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) : Int :=
  let totalGas := gas.foldl (· + ·) 0
  let totalCost := cost.foldl (· + ·) 0

  if totalGas < totalCost then
    -1
  else
    let rec loop (g c : List Int) (idx : Nat) (tank : Int) (start : Nat) : Int :=
      match g, c with
      | [], [] => start
      | gi :: gs, ci :: cs =>
        let tank' := tank + gi - ci
        if tank' < 0 then
          loop gs cs (idx + 1) 0 (idx + 1)
        else
          loop gs cs (idx + 1) tank' start
      | _, _ => -1

    let zipped := List.zip gas cost
    let rec walk (pairs : List (Int × Int)) (i : Nat) (tank : Int) (start : Nat) : Int :=
      match pairs with
      | [] => start
      | (g, c) :: rest =>
        let newTank := tank + g - c
        if newTank < 0 then
          walk rest (i + 1) 0 (i + 1)
        else
          walk rest (i + 1) newTank start

    walk zipped 0 0 0

@[reducible]
def canCompleteCircuit_postcond (gas : List Int) (cost : List Int) (result: Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) : Prop :=
  let valid (start : Nat) := List.range gas.length |>.all (fun i =>
    let acc := List.range (i + 1) |>.foldl (fun t j =>
      let jdx := (start + j) % gas.length
      t + gas[jdx]! - cost[jdx]!) 0
    acc ≥ 0)
  (result = -1 → (List.range gas.length).all (fun start => ¬ valid start)) ∧
  (result ≥ 0 → result < gas.length ∧ valid result.toNat ∧ (List.range result.toNat).all (fun start => ¬ valid start))


theorem length_zip_le_left (l₁ l₂ : List Int) :
    (List.zip l₁ l₂).length ≤ l₁.length:= by 
aesop


end tmp