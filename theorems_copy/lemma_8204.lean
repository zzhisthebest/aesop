module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_8204
public def below_zero_precond (operations : List Int) : Prop :=
  True

public def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList

public def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
  let s := buildS operations
  let rec check_negative (lst : List Int) : Bool :=
    match lst with
    | []      => false
    | x :: xs => if x < 0 then true else check_negative xs
  let result := check_negative (s.toList)
  (s, result)

public def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))


public theorem array_mem_toList {a : Array Int} {x : Int} :
    x ∈ a.toList ↔ ∃ i, i < a.size ∧ a[i]! = x:= by 
sorry


end tmp_lemma_8204