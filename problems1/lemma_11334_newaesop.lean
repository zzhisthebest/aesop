import Aesop
set_option maxHeartbeats 0
namespace tmp
def isOdd (n : Int) : Bool :=
  n % 2 == 1

@[reducible, simp]
def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  True

def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  let indexedArray := a.mapIdx fun i x => (i, x)

  indexedArray.all fun (i, x) => !(isOdd i) || isOdd x

@[reducible, simp]
def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))


theorem Array.mem_iff_get {α} (as : Array α) (x : α) :
    x ∈ as ↔ ∃ i : Fin as.size, as[i] = x:= by 
  aesop?


end tmp