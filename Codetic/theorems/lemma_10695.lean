module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_10695
public def allCharactersSame_precond (s : String) : Prop :=
  True

public def allCharactersSame (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  match s.toList with
  | []      => true
  | c :: cs => cs.all (fun x => x = c)

public def allCharactersSame_postcond (s : String) (result: Bool) (h_precond : allCharactersSame_precond (s)) :=
  let cs := s.toList
  (result → List.Pairwise (· = ·) cs) ∧
  (¬ result → (cs ≠ [] ∧ cs.any (fun x => x ≠ cs[0]!)))


public theorem nonempty_spec (c : Char) (cs : List Char) :
    (cs.all (· = c) = true → List.Pairwise (· = ·) (c :: cs)) ∧
    (cs.all (· = c) = false →
        (c :: cs ≠ [] ∧ (c :: cs).any (· ≠ (c :: cs)[0]!))):= by 
sorry


end tmp_lemma_10695