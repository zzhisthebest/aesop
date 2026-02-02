import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def smallestMissingNumber_precond (s : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) s

def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  let rec findMissing (v : Nat) (l : List Nat) : Nat :=
    match l with
    | [] => v
    | x :: xs =>
      if x > v then v
      else if x = v then findMissing (v + 1) xs
      else findMissing v xs
  findMissing 0 s

@[reducible, simp]
def smallestMissingNumber_postcond (s : List Nat) (result: Nat) (h_precond : smallestMissingNumber_precond (s)) :=
  ¬ List.elem result s ∧ (∀ k : Nat, k < result → List.elem k s)


theorem not_mem_cons_of_ne {a n : Nat} {xs : List Nat}
    (hneq : a ≠ n) (hnot : ¬ List.elem n xs) :
    ¬ List.elem n (a :: xs):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp