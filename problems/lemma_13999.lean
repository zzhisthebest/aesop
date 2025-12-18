import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  True

def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
  let minLength := Nat.min str1.length str2.length
  let rec aux (idx : Nat) (acc : List Char) : List Char :=
    if idx < minLength then
      match str1[idx]?, str2[idx]? with
      | some c1, some c2 =>
          if c1 ≠ c2 then acc
          else aux (idx + 1) (acc ++ [c1])
      | _, _ => acc
    else acc
  aux 0 []

@[reducible, simp]
def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :=
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))


theorem get?_eq_some_of_lt (l : List α) (i : Nat) (h : i < l.length) :
    ∃ c, l[i]? = some c ∧ l.take (i+1) = l.take i ++ [c]:= by 
  aesop?
  aesop?(config := { useDefaultSimpSet := false })


end tmp