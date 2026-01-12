module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_9481
public def findFirstRepeatedChar_precond (s : String) : Prop :=
  True

public def findFirstRepeatedChar (s : String) (h_precond : findFirstRepeatedChar_precond (s)) : Option Char :=
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

public def findFirstRepeatedChar_postcond (s : String) (result: Option Char) (h_precond : findFirstRepeatedChar_precond (s)) :=
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    cs.count c ≥ 2 ∧
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    List.Pairwise (· ≠ ·) cs


public theorem count_ge_two_of_two_occurrences (xs : List Char) (c : Char)
    (h₁ : xs.idxOf c ≠ xs.length) (h₂ : xs.idxOf? c = some (xs.idxOf c + 1)) :
    2 ≤ xs.count c:= by 
sorry


end tmp_lemma_9481