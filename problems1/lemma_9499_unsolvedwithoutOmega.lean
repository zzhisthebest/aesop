import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def findFirstRepeatedChar_precond (s : String) : Prop :=
  True

def findFirstRepeatedChar (s : String) (h_precond : findFirstRepeatedChar_precond (s)) : Option Char :=
  let cs := s.toList
  let rec loop (i : Nat) (seen : Std.HashSet Char) : Option Char :=
    if i < cs.length then
      let c := cs[i]!
      if seen.contains c then
        some c
      else
        loop (i + 1) (seen.insert c)
    else
      none
  loop 0 Std.HashSet.empty

@[reducible, simp]
def findFirstRepeatedChar_postcond (s : String) (result: Option Char) (h_precond : findFirstRepeatedChar_precond (s)) :=
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    cs.count c ≥ 2 ∧
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    List.Pairwise (· ≠ ·) cs


theorem pairwise_of_nodup {l : List α} (h : l.Nodup) :
  List.Pairwise (· ≠ ·) l:= by 
aesop?(config := { enableGrind := false })


end tmp