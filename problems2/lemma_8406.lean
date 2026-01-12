import Aesop
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


theorem any_of_mem_pred {l : List Char} {c : Char}
    (hmem : c ∈ l) (hcond : c = 'z' ∨ c = 'Z') :
    l.any (fun c => c = 'z' || c = 'Z') = true:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp