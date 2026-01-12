import Aesop
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


theorem array_all_iff_forall (n : Int) (a : Array Int) :
    (∀ i, (hi : i < a.size) → n > a[i]) ↔ a.all (fun x => n > x):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp