import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  True

def partitionEvensOdds (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) : (List Nat × List Nat) :=
  let rec helper (nums : List Nat) : (List Nat × List Nat) :=
    match nums with
    | [] => ([], [])
    | x :: xs =>
      let (evens, odds) := helper xs
      if x % 2 == 0 then (x :: evens, odds)
      else (evens, x :: odds)
  helper nums

@[reducible]
def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : partitionEvensOdds_precond (nums)): Prop :=
  let evens := result.fst
  let odds := result.snd
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)


theorem filter_all_eq (p : Nat → Bool) (l : List Nat) :
    (l.filter p).all p = true:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp