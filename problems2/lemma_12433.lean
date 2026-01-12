import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  True

def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  if a = b then true else false

@[reducible, simp]
def Compare_postcond (a : Int) (b : Int) (result: Bool) (h_precond : Compare_precond (a) (b)) :=
  (a = b → result = true) ∧ (a ≠ b → result = false)


theorem compare_eq_true (a b : Int) (h_eq : a = b) :
    Compare a b (by trivial : Compare_precond a b) = true:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp