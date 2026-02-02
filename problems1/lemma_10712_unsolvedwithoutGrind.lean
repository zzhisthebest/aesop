import Codetic
open TheoremsForCodeVerification
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def allCharactersSame_precond (s : String) : Prop :=
  True

def allCharactersSame (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  match s.toList with
  | []      => true
  | c :: cs => cs.all (fun x => x = c)
@[simp]
theorem pairwise_of_forall_eq
  {α : Type} (c : α) (l : List α)
  (h : ∀ a ∈ l, a = c) :
  List.Pairwise (· = ·) l := by
  sorry
@[reducible, simp]
def allCharactersSame_postcond (s : String) (result: Bool) (h_precond : allCharactersSame_precond (s)) :=
  let cs := s.toList
  (result → List.Pairwise (· = ·) cs) ∧
  (¬ result → (cs ≠ [] ∧ cs.any (fun x => x ≠ cs[0]!)))


theorem pairwise_of_all_eq (c : Char) (cs : List Char)
    (h : cs.all (fun x => x = c)) : List.Pairwise (· = ·) (c :: cs):= by
codetic?(config:={enableGrind:=false})
have: a'=c:=by
  codetic?(config:={enableGrind:=false})
codetic?(config:={enableGrind:=false})




--可以看出codetic的缺陷，但提不出定理
end tmp
