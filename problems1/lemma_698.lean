import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def increasingTriplet_precond (nums : List Int) : Prop :=
  True

def increasingTriplet (nums : List Int) (h_precond : increasingTriplet_precond (nums)) : Bool :=
  let rec lengthCheck : List Int → Nat → Nat
    | [], acc => acc
    | _ :: rest, acc => lengthCheck rest (acc + 1)

  let len := lengthCheck nums 0

  if len < 3 then
    false
  else
    let rec loop (xs : List Int) (first : Int) (second : Int) : Bool :=
      match xs with
      | [] => false
      | x :: rest =>
        let nextFirst := if x ≤ first then x else first
        let nextSecond := if x > first ∧ x ≤ second then x else second
        if x ≤ first then
          loop rest nextFirst second
        else if x ≤ second then
          loop rest first nextSecond
        else
          true
    match nums with
    | [] => false
    | _ :: rest1 =>
      match rest1 with
      | [] => false
      | _ :: rest2 =>
        match rest2 with
        | [] => false
        | _ =>
          loop nums 2147483647 2147483647

@[reducible]
def increasingTriplet_postcond (nums : List Int) (result: Bool) (h_precond : increasingTriplet_precond (nums)) : Prop :=
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))


theorem loop_never_nil (xs : List Int) (a b : Int) :
    (match xs with
     | [] => false
     | x :: rest => true) = true ∨ xs = []:= by 
aesop?(config := { enableGrind := false })


end tmp