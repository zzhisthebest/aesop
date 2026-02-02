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
@[simp]
theorem pairwise_of_forall_eq
  {α : Type} (c : α) (l : List α)
  (h : ∀ a ∈ l, a = c) :
  List.Pairwise (· = ·) l := by
  codetic


theorem pairwise_of_forall_eq1 (c : Char) (l : List Char)
    (h : ∀ a ∈ l, a = c) : List.Pairwise (· = ·) l:= by
-- induction l with
-- | @nil => simp_all only [List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil]
-- | @cons a
--   a_1 =>
--   simp_all only [List.mem_cons, true_or, or_true, implies_true, forall_const, forall_eq_or_imp, List.pairwise_cons,
--     and_true]
--   intro a' a_2
--   obtain ⟨left, right⟩ := h
--   subst left
--   rename_i tail_ih
--   clear tail_ih
--   grind
codetic?(config := { enableGrind := false })


end tmp
