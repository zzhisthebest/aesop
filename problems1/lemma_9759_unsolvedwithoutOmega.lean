import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isDivisibleBy11_precond (n : Int) : Prop :=
  True

def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  n % 11 == 0

@[reducible, simp]
def isDivisibleBy11_postcond (n : Int) (result: Bool) (h_precond : isDivisibleBy11_precond (n)) :=
  (result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))


theorem false_result_implies_forall_not (n : Int)
    (h : isDivisibleBy11 n (by trivial) = false) :
    ∀ k : Int, ¬ n = 11 * k:= by 
codetic?(config := { enableGrind := false })


end tmp