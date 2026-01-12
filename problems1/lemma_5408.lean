import Aesop
set_option maxHeartbeats 0
namespace tmp
def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower

@[reducible]
def allVowels_precond (s : String) : Prop :=
  True

def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  let chars := normalize_str s
  let vowelSet := ['a', 'e', 'i', 'o', 'u']
  vowelSet.all (fun v => chars.contains v)

@[reducible]
def allVowels_postcond (s : String) (result: Bool) (h_precond : allVowels_precond (s)) : Prop :=
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))


theorem vowelList_eq (chars : List Char) :
    (let vowelSet := ['a', 'e', 'i', 'o', 'u'];
     vowelSet.all (fun v => chars.contains v))
      =
    List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v):= by 
aesop?(config := { enableGrind := false })


end tmp