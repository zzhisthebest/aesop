import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  True

def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  let cleaned : List Char :=
    s.data.filter (fun c => c.isAlpha || c.isDigit)
      |>.map Char.toLower

  let n := cleaned.length
  let startIndex := 0
  let endIndex := if n = 0 then 0 else n - 1

  let rec check (l r : Nat) : Bool :=
    if l >= r then
      true
    else if cleaned[l]? = cleaned[r]? then
      check (l + 1) (r - 1)
    else
      false

  check startIndex endIndex

@[reducible]
def palindromeIgnoreNonAlnum_postcond (s : String) (result: Bool) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Prop :=
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
let forward := cleaned
let backward := cleaned.reverse

if result then
  forward = backward
else
  forward ≠ backward


theorem get?_in_bounds (l : List α) (i : Nat) (h : i < l.length) :
    l[i]? = some (l.get ⟨i, h⟩):= by 
aesop?(config := { enableGrind := false })


end tmp