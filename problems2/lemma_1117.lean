import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isPalindrome_precond (s : String) : Prop :=
  True

def isPalindrome (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
  let length := s.length

if length <= 1 then
  true
else
  let arr := s.toList

  let rec checkIndices (left : Nat) (right : Nat) (chars : List Char) : Bool :=
    if left >= right then
      true
    else
      match chars[left]?, chars[right]? with
      | some cLeft, some cRight =>
        if cLeft == cRight then
          checkIndices (left + 1) (right - 1) chars
        else
          false
      | _, _ => false
  let approach1 := checkIndices 0 (length - 1) arr

  let rec reverseList (acc : List Char) (xs : List Char) : List Char :=
    match xs with
    | []      => acc
    | h :: t  => reverseList (h :: acc) t
  let reversed := reverseList [] arr
  let approach2 := (arr == reversed)

  approach1 && approach2

@[reducible, simp]
def isPalindrome_postcond (s : String) (result: Bool) (h_precond : isPalindrome_precond (s)) : Prop :=
  (result → (s.toList == s.toList.reverse)) ∧
  (¬ result → (s.toList ≠ [] ∧ s.toList != s.toList.reverse))


theorem length_le_one_iff_eq_reverse (l : List α) :
    l.length ≤ 1 → l = l.reverse:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp