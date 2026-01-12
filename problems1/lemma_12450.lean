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


theorem compare_postcond_left (a b : Int) (h_precond : Compare_precond a b)
    (h : a = b) : (a = b → Compare a b h_precond = true):= by 
aesop?(config := { enableGrind := false })


end tmp