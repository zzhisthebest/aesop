import Codetic
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

#check Array.getElem?_append_left
theorem get_append_left (a b : Array Int) (i : Nat) (hi : i < a.size) :
    (a ++ b)[i]! = a[i]!:= by
codetic?(config := { enableGrind := false })


end tmp
