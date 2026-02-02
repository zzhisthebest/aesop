import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def allCharactersSame_precond (s : String) : Prop :=
  True

def allCharactersSame (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  match s.toList with
  | []      => true
  | c :: cs => cs.all (fun x => x = c)

@[reducible, simp]
def allCharactersSame_postcond (s : String) (result: Bool) (h_precond : allCharactersSame_precond (s)) :=
  let cs := s.toList
  (result → List.Pairwise (· = ·) cs) ∧
  (¬ result → (cs ≠ [] ∧ cs.any (fun x => x ≠ cs[0]!)))


theorem all_eq_true_iff_forall_eq (l : List Char) (c : Char) :
    l.all (fun x => x = c) = true ↔ ∀ x ∈ l, x = c:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp