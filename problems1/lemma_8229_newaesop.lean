import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def below_zero_precond (operations : List Int) : Prop :=
  True

def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList

def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
  let s := buildS operations
  let rec check_negative (lst : List Int) : Bool :=
    match lst with
    | []      => false
    | x :: xs => if x < 0 then true else check_negative xs
  let result := check_negative (s.toList)
  (s, result)

@[reducible, simp]
def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))


theorem buildS_step (ops : List Int) (i : Nat) (hi : i < ops.length) :
    (buildS ops)[i+1]? =
      (buildS ops)[i]? >>= fun a => (ops.get? i).map (fun op => a + op):= by 
  aesop?


end tmp