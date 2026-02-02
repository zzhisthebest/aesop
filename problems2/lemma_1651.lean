import Codetic
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


theorem not_any_invalid_of_valid
    (digits : String)
    (hvalid : ∀ c ∈ digits.toList, c ∈ ['2','3','4','5','6','7','8','9']) :
    ¬ digits.toList.any (λ c => ¬ c ∈ ['2','3','4','5','6','7','8','9']):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp