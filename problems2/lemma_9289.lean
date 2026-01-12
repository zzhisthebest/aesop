import Aesop
set_option maxHeartbeats 0
namespace tmp
def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0

@[reducible, simp]
def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)

def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  let rec findFirstEvenOdd (i : Nat) (firstEven firstOdd : Option Nat) : Int :=
    if i < a.size then
      let x := a[i]!
      let firstEven := if firstEven.isNone && isEven x then some i else firstEven
      let firstOdd := if firstOdd.isNone && isOdd x then some i else firstOdd
      match firstEven, firstOdd with
      | some e, some o => a[e]! - a[o]!
      | _, _ => findFirstEvenOdd (i + 1) firstEven firstOdd
    else
      0
  findFirstEvenOdd 0 none none

@[reducible, simp]
def firstEvenOddDifference_postcond (a : Array Int) (result: Int) (h_precond : firstEvenOddDifference_precond (a)) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))


theorem updateFirstOdd (firstOdd : Option Nat) (i : Nat) (x : Int) :
    (if firstOdd.isNone && isOdd x then some i else firstOdd) =
      (if firstOdd = none ∧ isOdd x then some i else firstOdd):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp