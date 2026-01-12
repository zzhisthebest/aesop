import Aesop
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


theorem search_step (a : Array Int) (key : Int) (i : Nat) :
    (if h : i < a.size then
        if a[i]! = key then Int.ofNat i
        else (if h' : i+1 < a.size then
                if a[i+1]! = key then Int.ofNat (i+1)
                else (if h'' : i+2 < a.size then -1 else -1)
              else -1)
      else -1) =
    (if h : i < a.size then
        if a[i]! = key then Int.ofNat i
        else (if h' : i+1 < a.size then
                if a[i+1]! = key then Int.ofNat (i+1)
                else -1
              else -1)
      else -1):= by 
aesop?(config := { enableGrind := false })


end tmp