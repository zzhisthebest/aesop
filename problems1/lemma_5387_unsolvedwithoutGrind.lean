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


theorem toLower_eq_self_of_not_upper (c : Char) (h : ¬ ('A' ≤ c ∧ c ≤ 'Z')) :
    toLower c = c:= by
simp_all only [↓Char.isValue, not_and, Char.not_le, toLower, Bool.and_eq_true, decide_eq_true_eq, ite_eq_right_iff,
  and_imp]
intro a a_1
simp_all only [↓Char.isValue, forall_const]
sorry


end tmp
