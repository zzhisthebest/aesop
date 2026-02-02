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


theorem any_char_z_or_Z (l : List Char) :
    l.any (fun c => c = 'z' || c = 'Z') = true ↔
      ∃ x ∈ l, (x = 'z' ∨ x = 'Z'):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp