-- -----Description-----
-- This task requires writing a Lean 4 method that checks whether all characters in an input string are identical. The method should return true if every character in the string is the same, and false if at least one character differs. An empty string or a single-character string is considered to have all characters identical.
--
-- -----Input-----
-- The input consists of:
-- s: A string.
--
-- -----Output-----
-- The output is a Boolean value:
-- Returns true if every character in the string is identical.
-- Returns false if there is at least one differing character.
--

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
import Aesop
namespace tmp
@[reducible, simp]
def allCharactersSame_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def allCharactersSame (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  -- !benchmark @start code
  match s.toList with
  | []      => true
  | c :: cs => cs.all (fun x => x = c)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def allCharactersSame_postcond (s : String) (result: Bool) (h_precond : allCharactersSame_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  (result → List.Pairwise (· = ·) cs) ∧
  (¬ result → (cs ≠ [] ∧ cs.any (fun x => x ≠ cs[0]!)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem allCharactersSame_spec_satisfied (s: String) (h_precond : allCharactersSame_precond (s)) :
    allCharactersSame_postcond (s) (allCharactersSame (s) h_precond) h_precond := by
  -- !benchmark @start proof
  simp_all only [allCharactersSame_postcond, allCharactersSame, String.toList, Bool.not_eq_true, ne_eq,
    String.data_eq_nil_iff, List.getElem!_eq_getElem?_getD, Char.reduceDefault, ↓Char.isValue, decide_not,
    List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  simp_all only [allCharactersSame_precond, ↓Char.isValue]
  split
  next x heq =>
    simp_all only [String.data_eq_nil_iff, String.data_empty, List.Pairwise.nil, imp_self, Bool.true_eq_false,
      not_true_eq_false, List.not_mem_nil, List.length_nil, Nat.lt_irrefl, getElem?_pos, ↓Char.isValue,
      Option.getD_some, true_and, forall_false, and_self]
  next x c cs
    heq =>
    simp_all only [List.all_eq_true, decide_eq_true_eq, List.pairwise_cons, List.all_eq_false, List.mem_cons,
      List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, ↓Char.isValue, Option.getD_some,
      exists_eq_or_imp, not_true_eq_false, or_true, and_true, forall_exists_index, and_imp]
    apply And.intro
    · intro a
      apply And.intro
      · intro a' a_1
        grind
      · clear heq--不clear导致induction不成立。这个能解决的话，aesop可以直接证明这道题
        aesop
    · intro x_1 a a_1
      apply Aesop.BuiltinRules.not_intro
      intro a_2
      subst a_2
      simp_all only [String.data_empty, List.nil_eq, reduceCtorEq]


#check List.pairwise_of_forall
  -- !benchmark @end proof
