import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def iter_copy_precond (s : Array Int) : Prop :=
  True

def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc
    else
      acc
  loop 0 Array.empty

@[reducible, simp]
def iter_copy_postcond (s : Array Int) (result: Array Int) (h_precond : iter_copy_precond (s)) :=
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)


theorem take_succ_push (a : Array Int) {i : Nat} (hi : i < a.size) :
    a.take (i+1) = (a.take i).push a[i]!:= by 
aesop


end tmp