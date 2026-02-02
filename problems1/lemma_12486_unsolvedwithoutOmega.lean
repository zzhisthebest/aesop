import Codetic
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


theorem imp_ne_false (a b : Int) (result : Bool) (h_ne : a ≠ b) (h_res : result = false) :
    (a ≠ b → result = false):= by 
codetic?(config := { enableGrind := false })


end tmp