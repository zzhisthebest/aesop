import Aesop
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


theorem nonempty_and_exists_ne_of_not_all {c : Char} {cs : List Char}
    (h : cs.all (fun x => x = c) = false) :
    cs ≠ [] ∧ cs.any (fun x => x ≠ c) = true:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp