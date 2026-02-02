import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  True

def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  s.toList.any fun c => c = 'z' || c = 'Z'

@[reducible, simp]
def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result


theorem eq_or_eq_of_bool_true (c : Char) (h : (c = 'z' || c = 'Z') = true) :
    c = 'z' ∨ c = 'Z':= by 
codetic?(config := { enableGrind := false })


end tmp