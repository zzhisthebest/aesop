import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)

def minOperations (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) : Nat :=
  if k == 0 then 0 else
  let rec loop (remaining : List Nat) (collected : List Nat) (collected_count : Nat) (ops : Nat) : Nat :=
    match remaining with
    | [] => ops
    | head :: tail =>
      let ops' := ops + 1
      if head > 0 && head <= k && !(List.elem head collected) then
          let collected' := head :: collected
          let collected_count' := collected_count + 1
          if collected_count' == k then
            ops'
          else
            loop tail collected' collected_count' ops'
      else
        loop tail collected collected_count ops'
  loop nums.reverse [] 0 0

@[reducible, simp]
def minOperations_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : minOperations_precond (nums) (k)) : Prop :=
  let processed := (nums.reverse).take result
  let target_nums := (List.range k).map (· + 1)

  let collected_all := target_nums.all (fun n => List.elem n processed)

  let is_minimal :=
    if result > 0 then
      let processed_minus_one := (nums.reverse).take (result - 1)
      ¬ (target_nums.all (fun n => List.elem n processed_minus_one))
    else
      k == 0

  collected_all ∧ is_minimal


theorem all_cons (p : Nat → Bool) (x : Nat) (xs : List Nat) :
    List.all (x :: xs) p = (p x && List.all xs p):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp