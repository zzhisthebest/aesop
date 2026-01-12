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


theorem loop_one_step (s : Array Int) (i : Nat) (acc : Array Int)
    (hi : i < s.size) (hacc : acc = s.take i) :
    (if i < s.size then
        match s[i]? with
        | some v => (fun loop => loop (i+1) (acc.push v)) (fun j a => a)
        | none   => acc
      else acc) = s.take (i+1):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp