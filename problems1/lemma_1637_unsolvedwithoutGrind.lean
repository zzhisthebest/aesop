import Aesop
set_option maxHeartbeats 0
namespace tmp
def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

@[reducible]
def letterCombinations_precond (digits : String) : Prop :=
  True

def letterCombinations (digits : String) (h_precond : letterCombinations_precond (digits)) : List String :=
  let chars := digits.toList
  go chars
  where
    go : List Char → List String
    | [] => []
    | (d :: ds) =>
      let restCombinations := go ds
      let currentLetters := digitToLetters d
      match restCombinations with
      | [] => currentLetters.map (λ c => String.singleton c)
      | _ => currentLetters.flatMap (λ c => restCombinations.map (λ s => String.singleton c ++ s))

@[reducible]
def letterCombinations_postcond (digits : String) (result: List String) (h_precond : letterCombinations_precond (digits)) : Prop :=
  if digits.isEmpty then
    result = []
  else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then
    result = []
  else
    let expected := digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]
    result.length = expected.length ∧ result.all (λ s => s ∈ expected) ∧ expected.all (λ s => s ∈ result)


theorem any_invalid_false_iff (cs : List Char) :
    cs.any (λ c => ¬ c ∈ ['2','3','4','5','6','7','8','9']) = false
      ↔ ∀ c ∈ cs, digitToLetters c ≠ []:= by
simp_all only [↓Char.isValue, List.mem_cons, List.not_mem_nil, or_false, not_or, Bool.decide_and, decide_not,
  List.any_eq_false, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_and,
  Decidable.not_not, digitToLetters, ne_eq]
apply Iff.intro
· intro a c a_1
  apply Aesop.BuiltinRules.not_intro
  intro a_2
  split at a_2
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c => simp_all only [↓Char.isValue, reduceCtorEq]
  next c_1 x x_1 x_2 x_3 x_4 x_5 x_6
    x_7 =>
    simp_all only [↓Char.isValue, imp_false, not_false_eq_true]
    --grind

    revert a
    simp
    exists c
· intro a x a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8
  --grind
  by_contra
  revert a
  simp
  exists x
  simp_all


aesop?(config := { enableGrind := false })


end tmp
--提不出来定理
