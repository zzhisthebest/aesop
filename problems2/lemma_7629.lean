import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  a.size > 0

def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  a.all fun x => n > x

@[reducible, simp]
def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) (h_precond : isGreater_precond (n) (a)) :=
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result


theorem array_all_iff_forall (a : Array Int) (p : Int → Bool) :
    a.all p = true ↔ ∀ i, (hi : i < a.size) → p (a[i]) = true:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp