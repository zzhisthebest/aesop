import Codetic
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


theorem bool_not_or_eq_imp (p q : Bool) :
    (!p || q) = true ↔ (p → q):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp