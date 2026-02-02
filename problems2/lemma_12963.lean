import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Find_precond (a : Array Int) (key : Int) : Prop :=
  True

def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0

@[reducible, simp]
def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)


theorem outer_if_true {a : Array Int} {key : Int} {idx : Nat}
    (h : idx < a.size) :
    (if idx < a.size then (if a[idx]! = key then Int.ofNat idx else (0 : Int))
     else (-1 : Int)) = (if a[idx]! = key then Int.ofNat idx else (0 : Int)):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp